package org.semanticweb.more.reasoner;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.semanticweb.elk.owlapi.ElkReasonerFactory;
import org.semanticweb.more.lsignature.LogicFragment;
import org.semanticweb.more.lsignature.LsignatureManager;
import org.semanticweb.more.pagoda.PAGOdAClassificationManager;
import org.semanticweb.more.structural.forgettableRoles.ForgettableRoles;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.more.util.Utility;
import org.semanticweb.more.visitors.ELAxiomVisitor;
import org.semanticweb.more.visitors.ELKAxiomVisitor;
import org.semanticweb.owlapi.model.AddAxiom;
import org.semanticweb.owlapi.model.AddOntologyAnnotation;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLDataPropertyExpression;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLException;
import org.semanticweb.owlapi.model.OWLLiteral;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyChange;
import org.semanticweb.owlapi.model.OWLOntologyChangeListener;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;
import org.semanticweb.owlapi.model.RemoveAxiom;
import org.semanticweb.owlapi.model.RemoveOntologyAnnotation;
import org.semanticweb.owlapi.reasoner.AxiomNotInProfileException;
import org.semanticweb.owlapi.reasoner.BufferingMode;
import org.semanticweb.owlapi.reasoner.ClassExpressionNotInProfileException;
import org.semanticweb.owlapi.reasoner.FreshEntitiesException;
import org.semanticweb.owlapi.reasoner.FreshEntityPolicy;
import org.semanticweb.owlapi.reasoner.InconsistentOntologyException;
import org.semanticweb.owlapi.reasoner.IndividualNodeSetPolicy;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.ReasonerInterruptedException;
import org.semanticweb.owlapi.reasoner.TimeOutException;
import org.semanticweb.owlapi.reasoner.UnsupportedEntailmentTypeException;
import org.semanticweb.owlapi.util.InferredAxiomGenerator;
import org.semanticweb.owlapi.util.InferredEquivalentClassAxiomGenerator;
import org.semanticweb.owlapi.util.InferredOntologyGenerator;
import org.semanticweb.owlapi.util.InferredSubClassAxiomGenerator;
import org.semanticweb.owlapi.util.Version;

import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;
import uk.ac.ox.cs.pagoda.util.Timer;
import uk.ac.ox.cs.pagoda.util.Utility_PAGOdA;

public class MOReReasoner implements OWLReasoner {

	/** Original ontology **/
	protected final OWLOntology root_ontology;

	/** Working ontology **/
	protected OWLOntology ontology;
	protected final String iri_str_working_ontology = Utility.getOntologyID_workingOntology();
	protected final String iri_compmodule_ontology = Utility.getOntologyID_compModule();
	protected final String iri_lmodule_ontology = Utility.getOntologyID_Lmodule();

	protected OWLOntologyManager manager;

	/**
	 * We need to keep them to remove them from reasoner before reclassifying
	 * This can be avoided if incremental functionalities are implemented
	 **/
	protected OWLOntology lmodule_onto;
	protected OWLOntology compmodule_onto;

	protected LsignatureManager lSignatureManager;

	/** Listener to track ontology changes (Very important for Protege plugin) **/
	protected final OntologyChangeListener root_ontologyChangeListener;

	/** Changes if incremental classification **/
	protected final List<OWLOntologyChange> pendingChanges_root_ontology;

	protected OWL2ReasonerManager owl2reasonerManager = new OWL2ReasonerManager(null, null);
	protected OWLReasoner owl2reasoner;
	protected OWLReasoner lReasoner;
	protected PAGOdAClassificationManager pagoda;
	protected LogicFragment lightweightFragment = LogicFragment.ELK; 

	protected MOReReasonerConfiguration configuration;
	protected Statistics stats;
	protected boolean isMonitorUp;
	protected boolean anyChanceOfUnsatisfiability = true;//true by default
	protected boolean isBuffered = true;

	protected ClassificationStatus status = ClassificationStatus.NOT_CLASSIFIED;


	public MOReReasoner(OWLOntology ontlgy, MOReReasonerConfiguration config) {
		this.configuration = config;

		this.manager = ontlgy.getOWLOntologyManager();//OWLManager.createOWLOntologyManager();
		this.root_ontology = ontlgy;
		this.root_ontologyChangeListener = new OntologyChangeListener();
		root_ontology.getOWLOntologyManager().addOntologyChangeListener(root_ontologyChangeListener);
		this.pendingChanges_root_ontology = new ArrayList<OWLOntologyChange>();

		this.lSignatureManager= new LsignatureManager(configuration.integrateRanges, configuration.rewriteInverses); 

		stats = new Statistics(ontlgy, config.integrateRanges || config.rewriteInverses, config.useRDFox);	
		
		this.isMonitorUp = (configuration != null && configuration.getProgressMonitor() != null);

		loadOntology();
	}

	public MOReReasoner(OWLOntology ontlgy) {
		this(ontlgy, new MOReReasonerConfiguration());
	}
	
	//called from factory
	protected MOReReasoner(OWLOntology ontlgy, boolean isBuffered, MOReReasonerConfiguration config, OWL2ReasonerManager owl2ReasonerManager) {
		this(ontlgy,config);
		this.isBuffered = isBuffered;
		this.owl2reasonerManager = owl2ReasonerManager;
	}

	protected MOReReasoner(OWLOntology ontlgy, boolean isBuffered,
			MOReReasonerConfiguration config) {
		this(ontlgy, config);
	}
	
	

	@Override
	public Version getReasonerVersion() {
		return new Version(0, 0, 2, 0);//2.0 will be the first MORe integrated with PAGOdA
	}

	public String getReasonerVersionStr() {
		return getReasonerVersion().getMajor() + "." + getReasonerVersion().getMinor() + "." + getReasonerVersion().getPatch();
	}


	protected void loadOntology() {
		Logger_MORe.logInfo("loading ontology");
		clearStatus();
		try {
			Logger_MORe.logTrace(root_ontology.getSignature(true).size() + " entities in signature");
			Logger_MORe.logTrace(root_ontology.getObjectPropertiesInSignature(true).size() + " properties in signature");
			Logger_MORe.logTrace(root_ontology.getClassesInSignature(true).size() + " classes in signature");
			if (!root_ontology.getABoxAxioms(true).isEmpty())
				Logger_MORe.logInfo("all assertional axioms in this ontology will be ignored for the purpose of classification");

			Set<OWLAxiom> rtBoxAxioms = new HashSet<OWLAxiom>(root_ontology.getTBoxAxioms(true));
			rtBoxAxioms.addAll(root_ontology.getRBoxAxioms(true));
			ontology = manager.createOntology(rtBoxAxioms, IRI.create(iri_str_working_ontology));
			
			Logger_MORe.logTrace(ontology.getLogicalAxiomCount() + " axioms in working ontology before eliminating forgettable roles");
			
			if (configuration.eliminateForgettableRoles){
				ForgettableRoles rewriter = new ForgettableRoles();
				anyChanceOfUnsatisfiability = false;
				Collection<OWLAxiom> rewrittenAxioms = rewriter.rewrite(ontology);
				if (rewrittenAxioms != null){
					manager.removeOntology(ontology);
					ontology = manager.createOntology(new HashSet<OWLAxiom>(rewrittenAxioms), IRI.create(iri_str_working_ontology));
				}
				else
					anyChanceOfUnsatisfiability = true;				
			}

			includeLostSignature();
			
			Logger_MORe.logInfo(ontology.getLogicalAxiomCount() + " axioms in working ontology");
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}


	/**
	 * If ontology is reloaded then we should clear current status. e.g. unload
	 * ontology, reasoner, structures, etc... If incremental reasoning then the
	 * ontology may not be reloaded.
	 */
	protected void clearStatus() {
		status = ClassificationStatus.NOT_CLASSIFIED;
		pendingChanges_root_ontology.clear();
		disposeUsedReasoners();
		unloadWorkingOntology();
		unloadModules();
		lSignatureManager.clear();
	}
	protected void unloadWorkingOntology() {
		if (manager.contains(IRI.create(iri_str_working_ontology))) {
			manager.removeOntology(ontology);
			this.ontology = null;
		}
	}
	protected void unloadModules() {
		if (manager.contains(IRI.create(iri_compmodule_ontology))) {
			manager.removeOntology(compmodule_onto);
			compmodule_onto = null;
		}
		if (manager.contains(IRI.create(iri_lmodule_ontology))) {
			manager.removeOntology(lmodule_onto);
			lmodule_onto = null;
		}
	}
	/**
	 * When filtering ontology some signature entities may be lost if they are
	 * not referenced in any Tbox or RBox axiom
	 */
	protected void includeLostSignature() {
		// Lost entities which were not appearing neither in RBox nor Tbox axioms
		Set<OWLClass> signatureLost = new HashSet<OWLClass>(root_ontology.getClassesInSignature(true));
		signatureLost.removeAll(ontology.getClassesInSignature(true));

		Set<OWLAxiom> newSubTopAxioms = new HashSet<OWLAxiom>();
		for (OWLClass cls : signatureLost) {
			newSubTopAxioms.add(
					manager.getOWLDataFactory().getOWLSubClassOfAxiom(cls, manager.getOWLDataFactory().getOWLThing()));
			newSubTopAxioms.add(
					manager.getOWLDataFactory().getOWLDeclarationAxiom(cls));
		}

		manager.addAxioms(ontology, newSubTopAxioms);
		Logger_MORe.logDebug(signatureLost.size() + " classes in lost Signature");
		signatureLost.clear();
		newSubTopAxioms.clear();
	}


	public void classifyClasses() {

		flushChangesIfRequired();

		if (status == ClassificationStatus.NOT_CLASSIFIED) {

			try {
				disposeUsedReasoners();
				unloadModules();

				Timer t = new Timer();
				lSignatureManager.findLsignature(ontology, lightweightFragment, stats);
				stats.updateLsignatureTime(t.duration());
				
				
				//if the lSignature is not empty, then we first classify with ELK
				//if the ontology contains anything at all that could lead to contradiction
				//if it doesn't then there is no need chance of extending the lSignature even further; furthermore, if this is the case 
				//and the lSignature is empty then we won't need ELK at all and it would be a waste of time - even if it's just a few seconds
				
				//if there are potentially any unsatisfiable classes, we want to try and identify them with ELK so we can get them out of the way
				//also, if the compSignature is empty then we only need to use ELK for the whole ontology
				if (anyChanceOfUnsatisfiability || lSignatureManager.getCompSignatureClasses().isEmpty()){
					classifyWithLreasoner(true);
					if (anyChanceOfUnsatisfiability && !lSignatureManager.getCompSignatureClasses().isEmpty())
						lSignatureManager.updateLsignatureWithUnsatClasses(lReasoner);
				}
				else if (!lSignatureManager.getLsignatureClasses().isEmpty())
					classifyWithLreasoner(false);
				

				if (lSignatureManager.getCompSignatureClasses().isEmpty())
					status = ClassificationStatus.CLASSIFIED_BY_ELK;
				else{
					try{
						extractComplementModule();
						if (configuration.useRDFox)
							processWithRDFoxAndOWL2Reasoner();
						else
							processWithOWL2Reasoner(compmodule_onto, false);
					}
					catch (OWLOntologyCreationException e){
						e.printStackTrace();
					}
				}

//				if (!isConsistent())
//					Logger_MORe.logInfo("The input ontology is inconsistent.");
			} finally {
				// Final step
				if (isMonitorUp) {
					configuration.getProgressMonitor().reasonerTaskStopped();
				}
				
				stats.printStats();
			}
		}
	}


	protected void processWithRDFoxAndOWL2Reasoner() {

		stats.updateNaxiomsForPAGOdA(compmodule_onto.getAxiomCount());
		Timer t = new Timer();
		pagoda = new PAGOdAClassificationManager(
				compmodule_onto, 
				lSignatureManager.getCompSignatureClasses(), 
				configuration.useMultiStageMaterialisation);
		OWLOntology axiomsToFinish = pagoda.classify();		
		stats.updatePAGOdAtime(t.duration());
		stats.updatePairsDecidedByHermiT(pagoda.getNundecidedSubsumptionPairs());
		
		if (axiomsToFinish != null)
			processWithOWL2Reasoner(axiomsToFinish, true);
		else{
			if (lSignatureManager.getLsignatureClasses().isEmpty())
				status = ClassificationStatus.CLASSIFIED_BY_PAGODA;
			else
				status = ClassificationStatus.CLASSIFIED_BY_ELK_AND_PAGODA;
		}

	}

	protected void processWithOWL2Reasoner(OWLOntology axiomsForOWL2Reasoner, boolean afterUsingPAGOdA) {
		if (configuration.saveOntologyForOWL2Reasoner){
			
			stats.updateHermiTtime(-1);
			stats.updateNaxiomsForHermiT(axiomsForOWL2Reasoner.getAxiomCount());
			
			String originalDocumentIRI = manager.getOntologyDocumentIRI(root_ontology).toString();
			if (!originalDocumentIRI.startsWith("file:")) 
				originalDocumentIRI = "file:"+ Utility_PAGOdA.TempDirectory + "ontology";
			String documentIRI = ""; 
			if (originalDocumentIRI.lastIndexOf(".") > -1)
				documentIRI = originalDocumentIRI.substring(0, originalDocumentIRI.lastIndexOf("."));
			else
				documentIRI = originalDocumentIRI;
			documentIRI += "_moduleForOWL2Reasoner";
			if (configuration.suffixForSavedOntology != null)
				documentIRI += "_"+configuration.suffixForSavedOntology;
			documentIRI += ".owl";
			Utility.saveOntology(manager, axiomsForOWL2Reasoner, documentIRI);
			status = ClassificationStatus.UNFINISHED_CLASSIFICATION_TESTING;
		}
		else{
			stats.updateNaxiomsForHermiT(axiomsForOWL2Reasoner.getAxiomCount());
			Timer t = new Timer();
			owl2reasoner = owl2reasonerManager.getOWL2ReasonerInstance(axiomsForOWL2Reasoner);
			owl2reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
			stats.updateHermiTtime(t.duration());
			if (lSignatureManager.getLsignatureClasses().isEmpty()){
				if (afterUsingPAGOdA)
					status = ClassificationStatus.CLASSIFIED_BY_PAGODA_AND_HERMIT;
				else{
					status = ClassificationStatus.CLASSIFIED_BY_HERMIT;
					stats.updatePairsDecidedPAGOdAstyle(0);
				}
			}
			else{
				if (afterUsingPAGOdA)
					status = ClassificationStatus.CLASSIFIED_BY_ELK_PAGODA_AND_HERMIT;
				else {
					status = ClassificationStatus.CLASSIFIED_BY_ELK_AND_HERMIT;
					stats.updatePairsDecidedPAGOdAstyle(0);
				}
			}
		}
	}

	protected void classifyWithLreasoner(boolean wholeOntology) {
		Timer t = new Timer();
		Logger.getLogger("org.semanticweb.elk").setLevel(Level.OFF);
		if (wholeOntology)
			lReasoner = new ElkReasonerFactory().createReasoner(ontology);
		else{
			try{
				extractLmodule();
				lReasoner = new ElkReasonerFactory().createReasoner(lmodule_onto);
			}
			catch (OWLOntologyCreationException e){
				lReasoner = new ElkReasonerFactory().createReasoner(ontology);
			}
		}
		lReasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
		stats.updateELKtime(t.duration());
	}

	

	protected int nELaxioms() {
		int n = 0;
		ELAxiomVisitor visitor = new ELAxiomVisitor();
		for (OWLAxiom ax : ontology.getAxioms()) {
			ax.accept(visitor);
			if (visitor.isEL())
				n++;
		}
		return n;
	}

	protected int nELKaxioms() {
		int n = 0;
		ELKAxiomVisitor visitor = new ELKAxiomVisitor();
		for (OWLAxiom ax : ontology.getAxioms()) {
			ax.accept(visitor);
			if (visitor.isInFragment())
				n++;
		}
		return n;
	}

	protected boolean isFullyEL(Set<OWLAxiom> axioms) {
		ELAxiomVisitor elVisitor = new ELAxiomVisitor();
		boolean booleanAcc = true;
		Iterator<OWLAxiom> iterator = axioms.iterator();
		OWLAxiom axiom;
		while (booleanAcc && iterator.hasNext()) {
			axiom = iterator.next();
			axiom.accept(elVisitor);
			booleanAcc = booleanAcc && elVisitor.isEL();
		}
		return booleanAcc;
	}

	protected Set<OWLAxiom> turnHierarchyIntoAxioms(OWLReasoner r) {

		long t = System.currentTimeMillis();

		// from Ernesto
		List<InferredAxiomGenerator<? extends OWLAxiom>> gens = new ArrayList<InferredAxiomGenerator<? extends OWLAxiom>>();
		gens.add(new InferredSubClassAxiomGenerator());
		gens.add(new InferredEquivalentClassAxiomGenerator());

		OWLOntology inferredOntology;
		try {
			inferredOntology = manager.createOntology();
			InferredOntologyGenerator iog = null;

			iog = new InferredOntologyGenerator(r, gens);
			iog.fillOntology(manager, inferredOntology);

			t = System.currentTimeMillis() - t;
			Logger_MORe.logDebug(t + "ms for the hierarchy rewriting");

			return inferredOntology.getAxioms();

		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
			return null;
		}

	}

	protected void extractComplementModule() throws OWLOntologyCreationException {
		SyntacticLocalityModuleExtractor botModExtractor = new SyntacticLocalityModuleExtractor(
				manager, ontology, ModuleType.BOT);

		Set<OWLAxiom> compModule = botModExtractor.extract(
				new HashSet<OWLEntity>(lSignatureManager.getCompSignatureClasses()));
		compmodule_onto = manager.createOntology(compModule, IRI.create(iri_compmodule_ontology));

		Logger_MORe.logInfo(compmodule_onto.getAxiomCount() + " axioms in comp module");

	}

	protected void extractLmodule() throws OWLOntologyCreationException {
		SyntacticLocalityModuleExtractor botModExtractor = new SyntacticLocalityModuleExtractor(manager, ontology, ModuleType.BOT);
		Set<OWLAxiom> lModule = botModExtractor.extract(
				new HashSet<OWLEntity>(lSignatureManager.getLsignatureClasses()));
		lmodule_onto = manager.createOntology(lModule, IRI.create(iri_lmodule_ontology));
		Logger_MORe.logDebug(lmodule_onto.getAxiomCount() + " axioms in l-module");
	}

	
	private boolean checkSatisfiability(OWLClass c) {
		SyntacticLocalityModuleExtractor botModExtractor = new SyntacticLocalityModuleExtractor(
				manager, ontology, ModuleType.BOT);
		Set<OWLEntity> signature = new HashSet<OWLEntity>();
		signature.add(c);

		boolean isSat = true;

		try {
			MOReReasoner auxMORe = new MOReReasoner(
					botModExtractor.extractAsOntology(
							signature,
							IRI.create("http://org.semanticweb.more.orechallenge/moduleForSatisfiability")));

			isSat = !auxMORe.getUnsatisfiableClasses().contains(c);

			auxMORe.dispose();

		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		return isSat;
	}

	/**
	 * Uses a module with OWL 2 Reasoner to check if a class expression "c" is satisfiable 
	 */
	private boolean checkSatisfiability(OWLClassExpression c) {
		SyntacticLocalityModuleExtractor botModExtractor = new SyntacticLocalityModuleExtractor(
				manager, ontology, ModuleType.BOT);
		Set<OWLEntity> signature = new HashSet<OWLEntity>();
		signature.addAll(c.getSignature());

		boolean isSat = true;

		try {
			OWLReasoner auxOWLReasoner = owl2reasonerManager.getOWL2ReasonerInstance(
					botModExtractor.extractAsOntology(
							signature,
							IRI.create("http://org.semanticweb.more.orechallenge/moduleForSatisfiability")));

			isSat = auxOWLReasoner.isSatisfiable(c);

			auxOWLReasoner.dispose();

		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		return isSat;
	}

	protected void disposeUsedReasoners() {
		if (lReasoner != null) {
			lReasoner.dispose();
		}
		if (owl2reasoner != null){ 
			owl2reasoner.dispose();
		}
	}

	public Set<OWLClass> getLsignatureClasses() {
		return lSignatureManager.getLsignatureClasses();
	}


	// methods inherited from the OWLReasoner interface
	@Override
	public void finalize() {
		dispose();
	}

	@Override
	public void dispose() {
		// remove ontology change listener
		root_ontology.getOWLOntologyManager().removeOntologyChangeListener(
				root_ontologyChangeListener);
		// disposeUsedReasoners and others
		clearStatus();

	}

	// Ontology change management methods
	protected class OntologyChangeListener implements OWLOntologyChangeListener {
		@Override
		public void ontologiesChanged(List<? extends OWLOntologyChange> changes)
				throws OWLException {
			for (OWLOntologyChange change : changes) {
				if (!(change instanceof RemoveOntologyAnnotation || change instanceof AddOntologyAnnotation)) {
					pendingChanges_root_ontology.add(change);
				}
			}
		}
	}

	protected void flushChangesIfRequired() {
		if (!isBufferingMode() && !pendingChanges_root_ontology.isEmpty())
			// if (!pendingChanges_root_ontology.isEmpty())
			flush();
	}

	@Override
	public void flush() {
		if (!pendingChanges_root_ontology.isEmpty()) {

			// TODO Incremental method (ernesto)
			// if MORe incremenal
			// do incremental classification
			// else
			Logger_MORe.logInfo("Loading ontology in MORe: after flush");
			loadOntology();

			// We empty changes
			pendingChanges_root_ontology.clear();
		}
	}

	protected boolean isBufferingMode() {
		return isBuffered;
	}

	@Override
	public BufferingMode getBufferingMode() {
		if (isBufferingMode()) {
			return BufferingMode.BUFFERING;
		} else {
			return BufferingMode.NON_BUFFERING;
		}
	}

	@Override
	public Set<OWLAxiom> getPendingAxiomAdditions() {
		Set<OWLAxiom> added = new HashSet<OWLAxiom>();
		for (OWLOntologyChange change : pendingChanges_root_ontology) {
			if (change instanceof AddAxiom) {
				added.add(change.getAxiom());
			}
		}
		return added;
	}

	@Override
	public Set<OWLAxiom> getPendingAxiomRemovals() {
		Set<OWLAxiom> removed = new HashSet<OWLAxiom>();
		for (OWLOntologyChange change : pendingChanges_root_ontology) {
			if (change instanceof RemoveAxiom) {
				removed.add(change.getAxiom());
			}
		}
		return removed;
	}

	@Override
	public List<OWLOntologyChange> getPendingChanges() {
		return pendingChanges_root_ontology;
	}

	// END: Ontology change management methods

	@Override
	public Node<OWLClass> getBottomClassNode() {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public Node<OWLDataProperty> getBottomDataPropertyNode() {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public Node<OWLObjectPropertyExpression> getBottomObjectPropertyNode() {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public NodeSet<OWLClass> getDataPropertyDomains(OWLDataProperty arg0,
			boolean arg1) throws InconsistentOntologyException,
			FreshEntitiesException, ReasonerInterruptedException,
			TimeOutException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null; 
	}

	@Override
	public Set<OWLLiteral> getDataPropertyValues(OWLNamedIndividual arg0,
			OWLDataProperty arg1) throws InconsistentOntologyException,
			FreshEntitiesException, ReasonerInterruptedException,
			TimeOutException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public NodeSet<OWLNamedIndividual> getDifferentIndividuals(
			OWLNamedIndividual arg0) throws InconsistentOntologyException,
			FreshEntitiesException, ReasonerInterruptedException,
			TimeOutException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public NodeSet<OWLClass> getDisjointClasses(OWLClassExpression ce)
			throws ReasonerInterruptedException, TimeOutException,
			FreshEntitiesException, InconsistentOntologyException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public NodeSet<OWLDataProperty> getDisjointDataProperties(
			OWLDataPropertyExpression arg0)
					throws InconsistentOntologyException, FreshEntitiesException,
					ReasonerInterruptedException, TimeOutException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public NodeSet<OWLObjectPropertyExpression> getDisjointObjectProperties(
			OWLObjectPropertyExpression arg0)
					throws InconsistentOntologyException, FreshEntitiesException,
					ReasonerInterruptedException, TimeOutException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public Node<OWLClass> getEquivalentClasses(OWLClassExpression arg0)
			throws InconsistentOntologyException,
			ClassExpressionNotInProfileException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		//		classifyClasses();
		//		switch (classified) {
		//		case classifiedWithElk:
		//			return lReasoner.getEquivalentClasses(arg0);
		//		case classifiedWithOWL2Reasoner:
		//			return owl2reasoner.getEquivalentClasses(arg0);
		//		default:
		//			LogOutput.printAlways("Classification not computed yet: getEquivalentClasses");
		//			//return null;
		//			return new OWLClassNode();
		//		}
		//
		//		// if (lSignature.contains(arg0))
		//		// return elk.getEquivalentClasses(arg0);
		//		// else
		//		// return hermiT.getEquivalentClasses(arg0);
		//TODO redo for new framework
		return null;
	}

	@Override
	public Node<OWLDataProperty> getEquivalentDataProperties(
			OWLDataProperty arg0) throws InconsistentOntologyException,
			FreshEntitiesException, ReasonerInterruptedException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public Node<OWLObjectPropertyExpression> getEquivalentObjectProperties(
			OWLObjectPropertyExpression arg0)
					throws InconsistentOntologyException, FreshEntitiesException,
					ReasonerInterruptedException, TimeOutException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public FreshEntityPolicy getFreshEntityPolicy() {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public IndividualNodeSetPolicy getIndividualNodeSetPolicy() {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public NodeSet<OWLNamedIndividual> getInstances(OWLClassExpression arg0,
			boolean arg1) throws InconsistentOntologyException,
			ClassExpressionNotInProfileException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public Node<OWLObjectPropertyExpression> getInverseObjectProperties(
			OWLObjectPropertyExpression arg0)
					throws InconsistentOntologyException, FreshEntitiesException,
					ReasonerInterruptedException, TimeOutException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public NodeSet<OWLClass> getObjectPropertyDomains(
			OWLObjectPropertyExpression arg0, boolean arg1)
					throws InconsistentOntologyException, FreshEntitiesException,
					ReasonerInterruptedException, TimeOutException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public NodeSet<OWLClass> getObjectPropertyRanges(
			OWLObjectPropertyExpression arg0, boolean arg1)
					throws InconsistentOntologyException, FreshEntitiesException,
					ReasonerInterruptedException, TimeOutException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public NodeSet<OWLNamedIndividual> getObjectPropertyValues(
			OWLNamedIndividual arg0, OWLObjectPropertyExpression arg1)
					throws InconsistentOntologyException, FreshEntitiesException,
					ReasonerInterruptedException, TimeOutException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public Set<InferenceType> getPrecomputableInferenceTypes() {
		Set<InferenceType> sol = new HashSet<InferenceType>();
		sol.add(InferenceType.CLASS_HIERARCHY);
		return sol;
	}

	@Override
	public String getReasonerName() {
		return "MORe";
	}

	@Override
	public OWLOntology getRootOntology() {
		return ontology;
	}

	
	public Set<OWLClass> getAllSuperClasses(OWLClass c) throws InconsistentOntologyException,
			ClassExpressionNotInProfileException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		classifyClasses();
		Set<OWLClass> ret;
		switch (status) {
		case CLASSIFIED_BY_ELK:
			ret = lReasoner.getSuperClasses(c, false).getFlattened();
			ret.addAll(lReasoner.getEquivalentClasses(c).getEntitiesMinus(c));
			return ret;
		case CLASSIFIED_BY_HERMIT:
			ret = owl2reasoner.getSuperClasses(c, false).getFlattened();
			ret.addAll(owl2reasoner.getEquivalentClasses(c).getEntitiesMinus(c));
			return ret; 
		case CLASSIFIED_BY_PAGODA:
			ret = pagoda.getAllSuperClasses(c);
			if (ret.size() == 1 && ret.iterator().next().isOWLNothing()){
				ret.iterator().remove();
				ret.addAll(ontology.getClassesInSignature(true));
			}
			return ret;
		case CLASSIFIED_BY_ELK_AND_PAGODA:
			if (lSignatureManager.getLsignatureClasses().contains(c)){
				if (lReasoner.getUnsatisfiableClasses().contains(c))
					ret = ontology.getClassesInSignature(true);
				else{
					ret = lReasoner.getSuperClasses(c, false).getFlattened();
					ret.addAll(lReasoner.getEquivalentClasses(c).getEntitiesMinus(c));
				}
				return ret;
			}
			else{
				ret = pagoda.getAllSuperClasses(c);
				if (ret.size() == 1 && ret.iterator().next().isOWLNothing()){
					ret.iterator().remove();
					ret.addAll(ontology.getClassesInSignature(true));
				}
				return ret;
			}
		case CLASSIFIED_BY_ELK_AND_HERMIT:
			if (lSignatureManager.getLsignatureClasses().contains(c)){
				if (lReasoner.getUnsatisfiableClasses().contains(c))
					ret = ontology.getClassesInSignature(true);
				else{
					ret = lReasoner.getSuperClasses(c, false).getFlattened();
					ret.addAll(lReasoner.getEquivalentClasses(c).getEntitiesMinus(c));
				}
				return ret;
			}
			else{
				if (owl2reasoner.getUnsatisfiableClasses().contains(c))
					ret = ontology.getClassesInSignature(true);
				else{
					ret = owl2reasoner.getSuperClasses(c, false).getFlattened();
					ret.addAll(owl2reasoner.getEquivalentClasses(c).getEntitiesMinus(c));
				}
				return ret;
			}
		case CLASSIFIED_BY_ELK_PAGODA_AND_HERMIT:
			if (lSignatureManager.getLsignatureClasses().contains(c)){
				if (lReasoner.getUnsatisfiableClasses().contains(c))
					ret = ontology.getClassesInSignature(true);
				else{
					ret = lReasoner.getSuperClasses(c, false).getFlattened();
					ret.addAll(lReasoner.getEquivalentClasses(c).getEntitiesMinus(c));
				}
				return ret;
			}
			else{
				ret = pagoda.getAllSuperClasses(c);
				if (ret.size() == 1 && ret.iterator().next().isOWLNothing()){
					ret.iterator().remove();
					ret.addAll(ontology.getClassesInSignature(true));
				}
				if (!pagoda.fullyClassifies(c)){
					ret.addAll(owl2reasoner.getSuperClasses(c, false).getFlattened());
					ret.addAll(owl2reasoner.getEquivalentClasses(c).getEntitiesMinus(c));
				}
				return ret;
			}
		case CLASSIFIED_BY_PAGODA_AND_HERMIT:
			ret = pagoda.getAllSuperClasses(c);
			if (ret.size() == 1 && ret.iterator().next().isOWLNothing()){
				ret.iterator().remove();
				ret.addAll(ontology.getClassesInSignature(true));
			}
			if (!pagoda.fullyClassifies(c)){
				if (owl2reasoner.getUnsatisfiableClasses().contains(c))
					ret = ontology.getClassesInSignature(true);
				else{
					ret.addAll(owl2reasoner.getSuperClasses(c, false).getFlattened());
					ret.addAll(owl2reasoner.getEquivalentClasses(c).getEntities());
				}
			}
			return ret;
		default:
			Logger_MORe.logInfo("Classification not computed");
			return new HashSet<OWLClass>();
		}
	}
	

	public Set<OWLClass> getAllUnsatisfiableClasses()
			throws ReasonerInterruptedException, TimeOutException,
			InconsistentOntologyException {
		classifyClasses();
		Set<OWLClass> ret;
		switch (status) {
		case CLASSIFIED_BY_ELK:
			return lReasoner.getUnsatisfiableClasses().getEntities();
		case CLASSIFIED_BY_HERMIT:
			return owl2reasoner.getUnsatisfiableClasses().getEntities();
		case CLASSIFIED_BY_PAGODA:
			return pagoda.getUnsatisfiableClasses();
		case CLASSIFIED_BY_ELK_AND_PAGODA:
			ret = lReasoner.getUnsatisfiableClasses().getEntities();
			ret.addAll(pagoda.getUnsatisfiableClasses());
			return ret;
		case CLASSIFIED_BY_ELK_AND_HERMIT:
			ret = lReasoner.getUnsatisfiableClasses().getEntities();
			ret.addAll(owl2reasoner.getUnsatisfiableClasses().getEntities());
			return ret;
		case CLASSIFIED_BY_ELK_PAGODA_AND_HERMIT:
			ret = lReasoner.getUnsatisfiableClasses().getEntities();
			ret.addAll(pagoda.getUnsatisfiableClasses());
			ret.addAll(owl2reasoner.getUnsatisfiableClasses().getEntities());
			return ret;
		case CLASSIFIED_BY_PAGODA_AND_HERMIT:
			ret = pagoda.getUnsatisfiableClasses();
			ret.addAll(owl2reasoner.getUnsatisfiableClasses().getEntities());
			return ret;
		default:
			Logger_MORe.logInfo("Classification not computed");
			return new HashSet<OWLClass>();
		}
	}
	
	@Override
	public NodeSet<OWLClass> getSuperClasses(OWLClassExpression arg0,
			boolean direct) throws InconsistentOntologyException,
			ClassExpressionNotInProfileException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		//TODO
		try{
			throw new Exception("not supported: use method getAllSuperClasses(OWLClass c) instead");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public Node<OWLClass> getUnsatisfiableClasses()
			throws ReasonerInterruptedException, TimeOutException,
			InconsistentOntologyException {
		//TODO
		try{
			throw new Exception("not supported: use method getAllUnsatisfiableClasses() instead");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}
	
	@Override
	public Node<OWLNamedIndividual> getSameIndividuals(OWLNamedIndividual arg0)
			throws InconsistentOntologyException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public NodeSet<OWLClass> getSubClasses(OWLClassExpression arg0, boolean direct)
			throws ReasonerInterruptedException, TimeOutException,
			FreshEntitiesException, InconsistentOntologyException,
			ClassExpressionNotInProfileException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public NodeSet<OWLDataProperty> getSubDataProperties(OWLDataProperty direct,
			boolean arg1) throws InconsistentOntologyException,
			FreshEntitiesException, ReasonerInterruptedException,
			TimeOutException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public NodeSet<OWLObjectPropertyExpression> getSubObjectProperties(
			OWLObjectPropertyExpression arg0, boolean direct)
					throws InconsistentOntologyException, FreshEntitiesException,
					ReasonerInterruptedException, TimeOutException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public NodeSet<OWLDataProperty> getSuperDataProperties(
			OWLDataProperty arg0, boolean direct)
					throws InconsistentOntologyException, FreshEntitiesException,
					ReasonerInterruptedException, TimeOutException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public NodeSet<OWLObjectPropertyExpression> getSuperObjectProperties(
			OWLObjectPropertyExpression arg0, boolean direct)
					throws InconsistentOntologyException, FreshEntitiesException,
					ReasonerInterruptedException, TimeOutException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public long getTimeOut() {
		return 0;
	}

	@Override
	public Node<OWLClass> getTopClassNode() {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public Node<OWLDataProperty> getTopDataPropertyNode() {		
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public Node<OWLObjectPropertyExpression> getTopObjectPropertyNode() {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public NodeSet<OWLClass> getTypes(OWLNamedIndividual arg0, boolean arg1)
			throws InconsistentOntologyException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public void interrupt() {
	}

	@Override
	public boolean isConsistent() throws ReasonerInterruptedException,
	TimeOutException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return false;
	}

	@Override
	public boolean isEntailed(OWLAxiom arg0)
			throws ReasonerInterruptedException,
			UnsupportedEntailmentTypeException, TimeOutException,
			AxiomNotInProfileException, FreshEntitiesException,
			InconsistentOntologyException {

		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return false;
	}

	@Override
	public boolean isEntailed(Set<? extends OWLAxiom> arg0)
			throws ReasonerInterruptedException,
			UnsupportedEntailmentTypeException, TimeOutException,
			AxiomNotInProfileException, FreshEntitiesException,
			InconsistentOntologyException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
		return false;
	}

	@Override
	public boolean isEntailmentCheckingSupported(AxiomType<?> arg0) {
//TODO
//		if (arg0 == AxiomType.SUBCLASS_OF) {
//			// LogOutput.printAlways("SUBCLASS_OF entailments are partially supported");
//			return true;
//		}
		return false;
	}

	@Override
	public boolean isPrecomputed(InferenceType arg0) {
		if (arg0 == InferenceType.CLASS_HIERARCHY) 
			if (status != ClassificationStatus.NOT_CLASSIFIED) 
				return true;
		return false;
	}

	@Override
	public boolean isSatisfiable(OWLClassExpression arg0)
			throws ReasonerInterruptedException, TimeOutException,
			ClassExpressionNotInProfileException, FreshEntitiesException,
			InconsistentOntologyException {

		if (arg0 instanceof OWLClass)
			return getAllUnsatisfiableClasses().contains(arg0);
		else
			//TODO
			try{
				throw new Exception("only supported for atomic classes");
			}
			catch (Exception e){
				e.printStackTrace();
			}
			return false;
	}

	@Override
	public void precomputeInferences(InferenceType... inferenceTypes)
			throws ReasonerInterruptedException, TimeOutException,
			InconsistentOntologyException {
		Set<InferenceType> requiredInferences = new HashSet<InferenceType>(
				Arrays.asList(inferenceTypes));
		if (requiredInferences.contains(InferenceType.CLASS_HIERARCHY))
			classifyClasses();
		else
			//TODO
			try{
				throw new Exception("precomputeInferences only supported for InferenceType.CLASS_HIERARCHY");
			}
			catch (Exception e){
				e.printStackTrace();
			}
	}

	public void printHierarchy(File outputFile) throws FileNotFoundException,
	OWLOntologyCreationException, OWLOntologyStorageException {
		//TODO
		try{
			throw new Exception("not supported");
		}
		catch (Exception e){
			e.printStackTrace();
		}
	}

}

enum ClassificationStatus{
	NOT_CLASSIFIED,
	CLASSIFIED_BY_ELK,
	CLASSIFIED_BY_ELK_AND_PAGODA,
	CLASSIFIED_BY_ELK_AND_HERMIT,
	CLASSIFIED_BY_ELK_PAGODA_AND_HERMIT,
	CLASSIFIED_BY_PAGODA_AND_HERMIT,
	CLASSIFIED_BY_HERMIT,
	CLASSIFIED_BY_PAGODA,
	UNFINISHED_CLASSIFICATION_TESTING
}