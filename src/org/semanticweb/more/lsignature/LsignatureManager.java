package org.semanticweb.more.lsignature;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.ForkJoinTask;

import org.semanticweb.more.reasoner.Statistics;
import org.semanticweb.more.structural.OWLNormalization4MORe;
import org.semanticweb.more.structural.inverseRewriting.Rewriter;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.more.util.Utility;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;
import uk.ac.ox.cs.pagoda.util.Timer;

public class LsignatureManager {

	protected Set<OWLClass> lSignatureClasses;
	protected Set<OWLEntity> lSignatureOther;
	protected Set<OWLClass> compSignatureClasses;
	protected Set<OWLEntity> compSignatureOther;

	public final boolean integrateRanges;
	public final boolean rewriteInverses;//if we rewrite inverses we will integrate ranges too always
	int totalNoDefinitions = 0;

	protected OWLOntology integratedRangesOntology;
	protected OWLOntology inverseRewritingOntology;

	protected int auxOntologyCounter = 0;
	protected Statistics stats;
	

	public LsignatureManager(boolean integrateRanges, boolean rewriteInverses){
		this.integrateRanges = integrateRanges;
		this.rewriteInverses = rewriteInverses;
	}

	public OWLOntology findLsignature(OWLOntology ontology, LogicFragment fragment, Statistics stats) {
		Timer t = new Timer();
		this.stats = stats;
		Logger_MORe.logInfo("extracting " + fragment.toString() + "-signature");
		OWLOntology ret = null;
		OWLOntologyManager manager = ontology.getOWLOntologyManager();
		try{
			ret = manager.createOntology();
			manager.addAxioms(ret, ontology.getAxioms());
		}
		catch (OWLOntologyCreationException e){
			e.printStackTrace();
		}
		lSignatureClasses = new HashSet<OWLClass>();
		lSignatureOther = new HashSet<OWLEntity>();
		compSignatureClasses = new HashSet<OWLClass>();
		compSignatureOther = new HashSet<OWLEntity>();

		LsignatureExtractorLauncher elkSignatureExtractorLauncher = null;
		LsignatureExtractorLauncher elkSignatureExtractorIntegratingRangesLauncher = null;
		LsignatureExtractorViaInverseRewritingLauncher elkSignatureExtractorRewritingInversesLauncher = null;

		ForkJoinPool executor = new ForkJoinPool();
		elkSignatureExtractorLauncher = new LsignatureExtractorLauncher(ontology, LogicFragment.ELK, false);
		executor.execute(elkSignatureExtractorLauncher);

		if (ret != null){
			//otherwise we have nowhere to return the axioms in the normalised ontologies necessary to really classify all the extra classses in the lSignature
			if (rewriteInverses){
				elkSignatureExtractorRewritingInversesLauncher = new LsignatureExtractorViaInverseRewritingLauncher(ontology, LogicFragment.ELK);
				executor.execute(elkSignatureExtractorRewritingInversesLauncher);
			}
			if (integrateRanges){
				elkSignatureExtractorIntegratingRangesLauncher = new LsignatureExtractorLauncher(ontology, LogicFragment.ELK, true);
				executor.execute(elkSignatureExtractorIntegratingRangesLauncher);
			}
			
			//check the output of the normal ELKsignature and cancel the other threads if the lSig is the whole signature
			initialiseLsignature((LsignatureExtractor) elkSignatureExtractorLauncher.join());

			if (compSignatureClasses.isEmpty())
				cancelTasks(elkSignatureExtractorIntegratingRangesLauncher, elkSignatureExtractorRewritingInversesLauncher);
			else{
				if (elkSignatureExtractorRewritingInversesLauncher != null && 
						extendLsignature((LsignatureExtractor) elkSignatureExtractorRewritingInversesLauncher.join()) > 0 ){
					manager.addAxioms(ret, ((LsignatureExtractorViaInverseRewritingLauncher) elkSignatureExtractorRewritingInversesLauncher).getOntology().getAxioms());
				}
				if (compSignatureClasses.isEmpty())
					cancelTasks(elkSignatureExtractorRewritingInversesLauncher);
				else if (elkSignatureExtractorIntegratingRangesLauncher != null &&
						extendLsignature((LsignatureExtractor) elkSignatureExtractorIntegratingRangesLauncher.join()) > 0){
					manager.addAxioms(ret, ((LsignatureExtractorLauncher) elkSignatureExtractorIntegratingRangesLauncher).getOntology().getAxioms());
				}
				
			}
			stats.updateLsignatureSize(lSignatureClasses.size(), true);
		}
		else{
			ret = ontology;
			initialiseLsignature((LsignatureExtractor) elkSignatureExtractorLauncher.join());
		}

		Logger_MORe.logInfo(lSignatureClasses.size() + "classes in lSignature");
		Logger_MORe.logDebug(lSignatureClasses.toString());
		Logger_MORe.logInfo(compSignatureClasses.size() + "classes in compSignature");

		//might be a good idea to try to isolate extra axioms in the normalisation/rewriting - is this possible/worth the effort?
		//check the order in which we try to extend the lSignature with each of the rewritten ontologies and consider if one may be better that the other
		Logger_MORe.logDebug(t.duration() + "s to find Lsignature");
		
		return ret;

	}

	public void updateLsignatureWithUnsatClasses(OWLReasoner reasoner){
		Set<OWLClass> unsatClasses = reasoner.getBottomClassNode().getEntities(); 
		if (lSignatureClasses.addAll(unsatClasses))
			compSignatureClasses.removeAll(unsatClasses);
	}

	public Set<OWLClass> getLsignatureClasses(){
		return lSignatureClasses;
	}
	public Set<OWLEntity> getLsignatureOtherEntities(){
		return lSignatureOther;
	}
	public Set<OWLClass> getCompSignatureClasses(){
		return compSignatureClasses;
	}
	public Set<OWLEntity> getCompSignatureOtherEntities(){
		return compSignatureOther;
	}


	public void clear(){
		if (lSignatureClasses != null) 
			lSignatureClasses.clear();
		if (lSignatureOther != null) 
			lSignatureOther.clear();
		if (compSignatureClasses != null)
			compSignatureClasses.clear();
		if (compSignatureOther != null)
			compSignatureOther.clear();
	}

	protected void initialiseLsignature(LsignatureExtractor extractor){
		for (OWLEntity e : extractor.getLsignature()){
			if (!Utility.isInternalPredicate(e.toString())){
				if (e instanceof OWLClass)
					lSignatureClasses.add((OWLClass) e);
				else
					lSignatureOther.add(e);
			}
		}
		for (OWLEntity e : extractor.getCompSignature()){
			if (!Utility.isInternalPredicate(e.toString())){
				if (e instanceof OWLClass)
					compSignatureClasses.add((OWLClass) e);
				else
					compSignatureOther.add(e);
			}
		}
		
		stats.updateLsignatureSize(lSignatureClasses.size(),false);
	}

	protected int extendLsignature(LsignatureExtractor extractor){
		int counter = 0;
		if (extractor != null){
			for (OWLEntity e : extractor.getLsignature()){
				if (!Utility.isInternalPredicate(e.toString())){
					if (e instanceof OWLClass){
						if (lSignatureClasses.add((OWLClass) e)){
							compSignatureClasses.remove((OWLClass) e);
							counter++;
						}
					}
					else{
						if (lSignatureOther.add(e))
							compSignatureOther.remove(e);
					}
				}
			}	
			Logger_MORe.logDebug(counter + " classes added to lSignature in LsignatureManager");
		}
		return counter;
	}

	protected void cancelTasks(ForkJoinTask<?>... tasks){
		for (ForkJoinTask<?> task : tasks){
			if (task != null){
				task.cancel(true);
				//				task.completeExceptionally(null);
			}
		}
	}

	class LsignatureExtractorLauncher extends ForkJoinTask<Object>{

		private static final long serialVersionUID = -6290155134070188986L;
		private OWLOntology ontology;
		private LogicFragment fragment;
		private LsignatureExtractor lSigExtractor = new LsignatureExtractor_reducedGreedyness();
		private boolean integrateRangesFirst;

		public LsignatureExtractorLauncher(OWLOntology ontology, LogicFragment fragment, boolean integrateRangesFirst){
			this.ontology = null;
			try {
				OWLOntologyManager manager = ontology.getOWLOntologyManager();
				this.ontology = manager.createOntology();
				manager.addAxioms(this.ontology, ontology.getAxioms());
			} catch (OWLOntologyCreationException e) {
				e.printStackTrace();
			}
			this.fragment = fragment;
			this.integrateRangesFirst = integrateRangesFirst;
		}


		@Override
		protected boolean exec() {
			Timer t = new Timer();
			if (ontology == null){
				lSigExtractor = null;
				return true;
			}
			if (integrateRangesFirst){
				OWLNormalization4MORe normalization = new OWLNormalization4MORe(ontology, true, false, false);
				Set<OWLAxiom> axioms = normalization.getNormalizedOntology();
				try {
					OWLOntologyManager manager = ontology.getOWLOntologyManager();
					ontology = manager.createOntology();
					manager.addAxioms(ontology,axioms);
				} catch (OWLOntologyCreationException e) {
					e.printStackTrace();
					lSigExtractor = null;
					return true;
				}
			}
			lSigExtractor.findLsignature(ontology, fragment);
			if (!integrateRangesFirst)
				stats.updateNelkAxioms(lSigExtractor.nAxiomsInFragment());
			Logger_MORe.logDebug(t.duration() + "s to find Lsignature with integrateRangesFirst=" + integrateRangesFirst);
			return true;
		}

		@Override
		public Object getRawResult() {
			return lSigExtractor;
		}

		public OWLOntology getOntology(){
			return ontology;
		}

		@Override
		protected void setRawResult(Object arg0) { }

	}

	class LsignatureExtractorViaInverseRewritingLauncher extends ForkJoinTask<Object>{

		private static final long serialVersionUID = -6290155134070188986L;
		private OWLOntology ontology;
		OWLOntologyManager manager;
		private LogicFragment fragment;
		private LsignatureExtractor extractor = new LsignatureExtractor_reducedGreedyness();

		public LsignatureExtractorViaInverseRewritingLauncher(OWLOntology ontology, LogicFragment fragment){
			this.ontology = null;
			try {
				manager = ontology.getOWLOntologyManager();
				this.ontology = manager.createOntology();
				manager.addAxioms(this.ontology, ontology.getAxioms());
			} catch (OWLOntologyCreationException e) {
				e.printStackTrace();
			}
			this.fragment = fragment;
		}

		protected boolean containsNonInternalClasses(Collection<OWLEntity> signature){
			boolean ret = false;
			for (OWLEntity e : signature){
				ret = e instanceof OWLClass && !Utility.isInternalPredicate(e.toString());
				if (ret) break;
			}
			return ret;
		}
		
		protected Set<OWLEntity> getNonInternalClasses(Collection<OWLEntity> signature){
			Set<OWLEntity> ret = new HashSet<OWLEntity>();
			for (OWLEntity e : signature)
				if (e instanceof OWLClass && !Utility.isInternalPredicate(e.toString()))
					ret.add(e);
			return ret;
		}

		@Override
		protected boolean exec() {
			Timer t = new Timer();
			if (ontology == null){
				extractor = null;
				return true;
			}
			IRI iri = IRI.create("http://www.cs.ox.ac.uk/isg/tools/MORe/ontologies/inverseRewritingModule.owl");
			extractor.findLsignature(ontology, LogicFragment.SHOIQ);
			if (containsNonInternalClasses(extractor.getCompSignature())){//then the ontology goes beyond SHOIQ and we need to work with a SHOIQ module rather than the whole ontology
				Set<OWLEntity> aux = getNonInternalClasses(extractor.getLsignature());
				if (aux.isEmpty()){
					extractor = null;
					Logger_MORe.logDebug(t.duration() + "s to find Lsignature with inverseRewriting (failed - empty SHOIQ-signature)");
					return true;	
				}
				SyntacticLocalityModuleExtractor moduleExtractor = new SyntacticLocalityModuleExtractor(
						manager, 
						ontology, 
						ModuleType.BOT);
				try {
//					ontology = manager.createOntology(iri);
//					manager.addAxioms(ontology, moduleExtractor.extract(aux));
					ontology = moduleExtractor.extractAsOntology(aux, iri);
				} catch (OWLOntologyCreationException e1) {
					extractor = null;
					e1.printStackTrace();
					Logger_MORe.logDebug(t.duration() + "s to find Lsignature with inverseRewriting (failed - exception creating a SHOIQ module)");
					return true;
				}
			}

			//if we get this far then we have a nonempty ontology (maybe module) that we need to normalize and then rewrite
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(ontology, true, true, true);
			Rewriter rewriter = new Rewriter(normalization.getNormalizedOntology(), normalization.getSortedGCIs());
			if (manager.contains(iri)) 
				manager.removeOntology(ontology);
			Set<OWLAxiom> rewrittenAxioms = rewriter.getRewrittenOntology();
			if (!rewriter.anyRewrittenRoles()){
				extractor = null;
				Logger_MORe.logDebug(t.duration() + "s to find Lsignature with inverseRewriting (failed - could not rewrite any roles)");
				return true;
			}
			try {
				ontology = manager.createOntology();
				manager.addAxioms(ontology, rewrittenAxioms);
				extractor = new LsignatureExtractor_reducedGreedyness();
				extractor.findLsignature(ontology, fragment);
			} catch (OWLOntologyCreationException e1) {
				extractor = null;
				e1.printStackTrace();
				Logger_MORe.logDebug(t.duration() + "s to find Lsignature with inverseRewriting (failed - exception creating ontology for rewritten axioms)");
				return true;
			}
			Logger_MORe.logDebug(t.duration() + "s to find Lsignature with inverseRewriting");
			return true;
		}

		@Override
		public Object getRawResult() {
			return extractor;
		}

		public OWLOntology getOntology() {
			return ontology;
		}

		@Override
		protected void setRawResult(Object arg0) { }

	}


	//	class NormalisationLauncher extends ForkJoinTask<Object>{
	//
	//		private static final long serialVersionUID = -6290155134070188986L;
	//		private OWLOntology ontology;
	//		private boolean rewriteInverses;
	//		private boolean integrateRanges;
	//		private Set<OWLAxiom> normalizedAxioms;
	//		
	//		public NormalisationLauncher(boolean rewriteInverses, boolean integrateRanges){
	//			this.rewriteInverses = rewriteInverses;
	//			this.integrateRanges = integrateRanges;
	//		}
	//
	//
	//		@Override
	//		protected boolean exec() {
	//			OWLNormalization4MORe normalization = new OWLNormalization4MORe(ontology, integrateRanges, rewriteInverses, rewriteInverses);
	//			normalizedAxioms = normalization.getNormalizedOntology();
	//			return true;
	//		}
	//		
	//		@Override
	//		public Object getRawResult() {
	//			return normalizedAxioms;
	//		}
	//
	//		@Override
	//		protected void setRawResult(Object arg0) { }
	//
	//	}
}
