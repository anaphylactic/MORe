package org.semanticweb.more.pagoda;

import java.io.File;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.HermiT.model.Individual;
import org.semanticweb.more.pagoda.rules.DatalogProgram4Classification;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.more.util.Utility;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;
import uk.ac.ox.cs.JRDFox.JRDFStoreException;
import uk.ac.ox.cs.JRDFox.store.TupleIterator;
import uk.ac.ox.cs.pagoda.hermit.DLClauseHelper;
import uk.ac.ox.cs.pagoda.multistage.MultiStageQueryEngine;
import uk.ac.ox.cs.pagoda.query.AnswerTuple;
import uk.ac.ox.cs.pagoda.query.AnswerTuples;
import uk.ac.ox.cs.pagoda.query.ClassificationQueryType;
import uk.ac.ox.cs.pagoda.query.GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly_supportingEquality;
import uk.ac.ox.cs.pagoda.query.MultiQueryRecord;
import uk.ac.ox.cs.pagoda.query.QueryManager;
import uk.ac.ox.cs.pagoda.query.QueryRecord;
import uk.ac.ox.cs.pagoda.query.QueryRecord4Classification;
import uk.ac.ox.cs.pagoda.reasoner.QueryReasoner;
import uk.ac.ox.cs.pagoda.reasoner.light.BasicQueryEngine;
import uk.ac.ox.cs.pagoda.reasoner.light.RDFoxTripleManager;
import uk.ac.ox.cs.pagoda.tracking.MultiQueryTracker;
import uk.ac.ox.cs.pagoda.tracking.TrackingRuleEncoder;
import uk.ac.ox.cs.pagoda.tracking.TrackingRuleEncoderDisjVar14Classification;
import uk.ac.ox.cs.pagoda.tracking.TrackingRuleEncoderWithGap4Classification;
import uk.ac.ox.cs.pagoda.util.MyPrefixes;
import uk.ac.ox.cs.pagoda.util.Timer;
import uk.ac.ox.cs.pagoda.util.Utility_PAGOdA;


public class PAGOdAClassificationManager extends QueryReasoner{//this class follows the structure of MyQueryReasoner in PAGOdA

	protected OWLOntology ontology; 
	OWLOntology reducedOntology;
	int currentOntologySize;	 
	Set<OWLClass> classesToClassify;//the set of classes whose classification is determined in here and possibly using the set of axioms that 'getAxiomsToFinish()' returns
	Set<OWLClass> classesWithGap;

	boolean multiStageTag;
	ClassificationQueryType queryType;

	BasicQueryEngine lowerStore = null;
	MultiStageQueryEngine lazyUpperStore = null;  
	BasicQueryEngine trackingStore = null;
	TrackingRuleEncoder encoder;

	IndividualManager indManager = new IndividualManager();
	ABoxManager aBoxManager;
	QueryManager4Classification queryManager = new QueryManager4Classification();

	DatalogProgram4Classification program;

	Set<QueryRecord4Classification> queryRecords = new HashSet<QueryRecord4Classification>();//this variable is redundant because all queries are stored in the QueryManager that any instance of this class possesses
	List<String> individualsWithContradictionsInLazyStore = new LinkedList<String>();
	Collection<String> predicatesWithGap = new HashSet<String>();
	Collection<String> individualsWithGap = new HashSet<String>();

	//	Map<AtomicConcept, Collection<AtomicConcept>> classificationGap = new HashMap<AtomicConcept, Collection<AtomicConcept>>();
	Set<OWLClass> unsatisfiableClasses = new HashSet<OWLClass>();
	
	int nUndecidedSubsumptionPairs;

	protected Timer t = new Timer();

	boolean error = false;

	public static PAGOdAClassificationManager create(OWLOntology o, Set<OWLClass> classesToClassify, boolean multiStage, ClassificationQueryType qType, boolean parallel){
		if (parallel)
			return new PAGOdAClassificationManager_parallel(o, classesToClassify, multiStage, qType);
		else 
			return new PAGOdAClassificationManager(o, classesToClassify, multiStage, qType);
	}

	public PAGOdAClassificationManager(OWLOntology o, Set<OWLClass> classesToClassify, boolean multiStage, ClassificationQueryType qType){
		multiStageTag = multiStage; 
		queryType = qType;
		dispose();
		lowerStore = new BasicQueryEngine("rl-lower-bound");
		trackingStore = new BasicQueryEngine("tracking"); //don't want any multiStage in my tracking store getUpperStore("tracking", false);
		aBoxManager = new ABoxManager(indManager);
		this.classesToClassify = classesToClassify;
		classesWithGap = classesToClassify;
		new File(Utility_PAGOdA.TempDirectory).mkdirs();
		loadOntology(o);
		reducedOntology = ontology;
		currentOntologySize = ontology.getAxiomCount();
	}
	public PAGOdAClassificationManager(OWLOntology o, Set<OWLClass> classesToClassify, ClassificationQueryType qType){
		this(o, classesToClassify, true, qType);
	}
	public void loadOntology(OWLOntology o){
		ontology = o; 
		program = new DatalogProgram4Classification(ontology, false);
//		if (Logger_MORe.getLevel() != null && Logger_MORe.getLevel().isGreaterOrEqual(Level.DEBUG)){
			Logger_MORe.logInfo("going to save programs");
			program.getUpper().save();
			program.getGeneral().save();
			program.getRLprogram().save();
			program.getELprogram().save();			
//		}

		if (multiStageTag && !program.getGeneral().isHorn())  
			lazyUpperStore =  new MultiStageQueryEngine("lazy-upper-bound", true, indManager);
		else
			multiStageTag = false;
	}

	protected boolean initData(){
		importData(program.getAdditionalDataFile());//assertional part of the input ontology - should probably be empty in our case? TODO check
		String initialAboxFile =  aBoxManager.createInstantiationABox(classesToClassify);
		if (initialAboxFile == null) return false;
		importData(initialAboxFile);
		aBoxManager.createSkolemABox(program.getAdditionalABoxFacts()); //we don't add the Skolem ABox to the group of ABoxes that need to be loaded into the triplestore from the very beginning because it needs to be added at a slightly different time
		return true;
	}

	public OWLOntology classify(){//returns null if the ontology is already fully classified and an ontology to finish the classification otherwise
		if (!initData()){
			nUndecidedSubsumptionPairs = classesToClassify.size()*(classesToClassify.size()+1);
			return ontology;
		}
		else{
			if (preprocess()){ //then the ontology has been fully classified by the tripleStore
				nUndecidedSubsumptionPairs = 0;
				return null;
			}

			if (initQueryRecords()){//must return true if we did indeed collect some queryRecords and there is something to track for.
				try{
					//nUndecidedSubsumptionPairs updated inside method initQueryRecords
					return getAxiomsToFinish(); 
				}
				catch (OWLOntologyCreationException e){
					e.printStackTrace();
					return reducedOntology;
				}
			}
			else{
				Logger_MORe.logError("preprocess returned false but no query record have been created - WHY??");
				return null;
			}
		}
	}
	public GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly_supportingEquality lazyGap;
	public GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly_supportingEquality gap;
	public GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly_supportingEquality[] getGaps(){//this is for debugging purposes
		return new GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly_supportingEquality[]{lazyGap, gap};
	}
	@Override
	public boolean preprocess() {//returns true if the ontology is already fully classified, false otherwise
		t.reset(); 
		Logger_MORe.logInfo("Preprocessing ontology for classification... ");
		String name = "instantiation ABox", instantiationDatafile = importedData.toString(); 

		lowerStore.importRDFData(name, instantiationDatafile);
		lowerStore.materialise("rl program", new File(program.getRLprogram().getOutputPath()), true);
		lowerStore.importRDFData("skolem data", aBoxManager.skolemABox_fileName);
		lowerStore.materialise("el program", new File(program.getELprogram().getOutputPath()), false);
		
		Utility.printAllTriples(lowerStore.getDataStore());
		Logger_MORe.logInfo("The number of sameAs assertions in RL lower store: " + lowerStore.getSameAsNumber());

		updateUnsatisfiableClasses();
		if (!unsatisfiableClasses.isEmpty())
			aBoxManager.updateInstantiationABox(classesToClassify);

		if (lazyUpperStore != null) {
			lazyUpperStore.importRDFData(name, instantiationDatafile);//if initialABox has been updated it will still be in the same file.
			lazyGap = new GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly_supportingEquality(lazyUpperStore, lowerStore);
			lazyUpperStore.materialiseMultiStage(program, aBoxManager.skolemABox_fileName, lazyGap, lowerStore, false);

			//before launching the trackingStore check if the gap is empty
			if (lazyGap.getNamedIndividualsWithGap().isEmpty()){
				return true;
			}
			else{
				individualsWithContradictionsInLazyStore = lazyGap.getNamedInstancesOfNothing();
				individualsWithGap = lazyGap.getNamedIndividualsWithGap();
				if (individualsWithGap.size() < classesToClassify.size()){
					updateClassesWithGapFromIndividualsWithGap();
					aBoxManager.updateInstantiationABox(individualsWithGap);
					indManager.updateActiveIndexes(individualsWithGap);
					if (updateUpperProgramWithGap(ModuleType.BOT))
						aBoxManager.updateSkolemABox(program.getAdditionalABoxFacts());
				}

				trackingStore.importRDFData(name, instantiationDatafile);
				gap = new GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly_supportingEquality(trackingStore, lowerStore); 
				trackingStore.materialise(program, aBoxManager.skolemABox_fileName, gap, lowerStore, indManager, false);

//				Utility.printAllTriples(trackingStore.getDataStore());

				//if there are any contradictions in the lazyUpperStore then we need to consider the predicatesWithGap given by the trackingStore
				if (individualsWithContradictionsInLazyStore.isEmpty()){
					//if there are no contradictions in the lazyUpperStore then the predicates with gap in the lazyUpperStore (plus owl:Nothing!!) are the only ones we need to consider
					predicatesWithGap = lazyGap.getPredicatesWithGap();
					predicatesWithGap.add(MyPrefixes.PAGOdAPrefixes.expandText("owl:Nothing"));
				}
				else
					predicatesWithGap = gap.getPredicatesWithGap();
				updateUpperProgramWithGap(ModuleType.TOP);
				//even if the program has changed after this there is not point in updating the skolemAbox file
				//because it won't get reloaded, all the skolem facts have been loaded already in the trackingStore
				gap.clear();//this only clears the iterator inside the gap, everything else remains intact so we can still access it
				lazyGap.clear();
				return false;
			}
		}
		else{
			trackingStore.importRDFData(name, instantiationDatafile);
			gap = new GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly_supportingEquality(trackingStore, lowerStore); 
			trackingStore.materialise(program, aBoxManager.skolemABox_fileName, gap, lowerStore, indManager, false);
			
//			Utility.printAllTriples(trackingStore.getDataStore());
			
//			System.out.println("named individualsWithGap");
//			for (String s :gap.getNamedIndividualsWithGap())
//				System.out.println(s);
//			System.out.println();
			
			if (gap.getNamedIndividualsWithGap().isEmpty())
				return true;
			else{
				predicatesWithGap = gap.getPredicatesWithGap(); 
				individualsWithGap = gap.getNamedIndividualsWithGap();
				if (individualsWithGap.size() < classesToClassify.size()){
					updateClassesWithGapFromIndividualsWithGap();
//					aBoxManager.updateInstantiationABox(individualsWithGap);
//					indManager.updateActiveIndexes(individualsWithGap);
					//I don't think we need to do the two things above in this case
					updateUpperProgramWithGap(ModuleType.STAR);
					//even if the program has changed after this there is not point in updating the skolemAbox file
					//because it won't get reloaded, all the skolem facts have been loaded already in the trackingStore
				}
				gap.clear();
				return false;
			}
		}
	}
	protected void updateClassesWithGapFromIndividualsWithGap() {
		classesWithGap.clear();
		for (String i : individualsWithGap)
			classesWithGap.add(indManager.getClass4Individual(i));
	}
	public Set<OWLClass> getClassesWithGap() {
		return classesWithGap;
	}
	protected boolean initQueryRecords(){
		if (queryType == ClassificationQueryType.PREDICATE){
			//		if (multiStageTag)
			//			individualsWithGap.clear();//we are going to refine this here//NO MORE NECESSARY
			for (String p : predicatesWithGap){
				String query = "select ?x where { " +
						"?x " + MyPrefixes.PAGOdAPrefixes.expandText("rdf:type") + " " + p + " }";
				QueryRecord4Classification queryRecord = null;
				//			if (p.contains("http://www.w3.org/2002/07/owl#Nothing")){
				//				if (p.equals("<http://www.w3.org/2002/07/owl#Nothing>"))
				//					queryRecord = getQueryManager().create(query,0);//we only need to consider the query for the normal bottom predicate - we only need to consider that one bottom predicate at all in general, but just in case
				//			}//we don't want to treat the query for bottom any differently - we don't want answers with skolem individuals - so we won't specify its ID of 0 at creation time
				//			else 
				if (!Utility.isInternalPredicate(p))
					queryRecord = ((QueryManager4Classification) getQueryManager()).create(query, ClassificationQueryType.PREDICATE, p);

				if (queryRecord != null){

					evaluate(queryRecord);
					//				if (multiStageTag)
					//					for (AnswerTuple tuple : queryRecord.getGapAnswerTuples()){
					//						String s = tuple.getRawTerm(0);
					//						if (multiStageTag && IndividualManager.isInstantiationIndividual(s))
					//							individualsWithGap.add(s);
					//					}//NO MORE NECESSARY

					if (!queryRecord.processed()){
						Logger_MORe.logDebug(queryRecord.getQueryEntity() + " has a Gap");
						for (AnswerTuple tuple : queryRecord.getGapAnswerTuples())
							Logger_MORe.logTrace(tuple.toString());
						queryRecords.add(queryRecord);
						nUndecidedSubsumptionPairs = nUndecidedSubsumptionPairs + queryRecord.getGapAnswerTuples().size();
					}
					t.reset();				
				}
			}			
		}
		else{
			Iterator<String> iter = individualsWithGap.iterator();
			while (iter.hasNext()){
				String ind = iter.next();
				String query = "select ?z where { " +
						ind + " " + MyPrefixes.PAGOdAPrefixes.expandText("rdf:type") + " ?z }";
				QueryRecord4Classification queryRecord = ((QueryManager4Classification) getQueryManager()).create(query, ClassificationQueryType.INDIVIDUAL, ind);
				evaluate(queryRecord);
				if (!queryRecord.processed()){
					Logger_MORe.logDebug(queryRecord.toString());
					for (AnswerTuple tuple : queryRecord.getGapAnswerTuples())
						Logger_MORe.logDebug(tuple.toString());
					queryRecords.add(queryRecord);
					classesWithGap.add(indManager.getClass4Individual(ind));
					nUndecidedSubsumptionPairs = nUndecidedSubsumptionPairs + queryRecord.getGapAnswerTuples().size();
				}
				else{
					iter.remove();
					Logger_MORe.logError("SHOULD WE BE HERE?? individualsWithGap should only contain individuals that do indeed have a gap");
				}
				t.reset();				
			}
			if (!queryRecords.isEmpty()){
				String bot = MyPrefixes.PAGOdAPrefixes.expandText("owl:Nothing");
				String query = "select ?x where { ?x " 
						+ MyPrefixes.PAGOdAPrefixes.expandText("rdf:type") + " " + bot + " }";
				QueryRecord4Classification queryRecord = ((QueryManager4Classification) getQueryManager()).create(query, ClassificationQueryType.PREDICATE, bot);
				evaluate(queryRecord);
				if (!queryRecord.processed()){
					Logger_MORe.logDebug(queryRecord.toString());
					for (AnswerTuple tuple : queryRecord.getGapAnswerTuples())
						Logger_MORe.logDebug(tuple.toString());
					queryRecords.add(queryRecord);
				}
				t.reset();
			}
		}
		return !queryRecords.isEmpty();
	}
	protected Set<QueryRecord4Classification> getQueryRecords(){
		return queryRecords;
	}

	protected String moduleSuffix = "";
	protected boolean updateUpperProgramWithGap(ModuleType moduleType){ //returns true if the upperProgram has been updated
		OWLOntologyManager manager = ontology.getOWLOntologyManager();
		OWLDataFactory factory = manager.getOWLDataFactory();
		
		//if we are doing multiStage materialisation we will do this before we do anything we the trackingStore, so we can simply
		//extract the module from ontology
		//if we are using only the tracking store, we will do this after normal materialisation, before tracking materialisation,
		//and then the Skolem constants need to be consistent with the ones used in the normal materialisation. For this it's not enough
		//to recover skolem constants from a map that matches tem with the corresponding DLClause because the DLClauses will have to be created
		//from scratch, and will most likely introduce different abbreviations. A solution in this case is to recover the DLClauses generated 
		//when we first loaded the ontology, turn them into axioms and extract any modules from the resulting ontology
		
		
		if (lazyUpperStore == null){
			Set<OWLAxiom> aux = new HashSet<OWLAxiom>();
			for (DLClause dlClause : program.getUpper().getClauses()){
				if (DLClauseHelper.isTautologyAboutDifferentFrom(dlClause))
					continue;
				OWLAxiom ax = program.getUpper().getEquivalentAxiom(dlClause); 
//				if (ax instanceof OWLSubClassOfAxiom && ((OWLSubClassOfAxiom) ax).getSubClass().isOWLThing())
//					System.out.println(dlClause.toString());
				aux.add(ax);
			}
			try {
				reducedOntology = manager.createOntology(aux, IRI.create(Utility.getOntologyID_DLontology()));
			} catch (OWLOntologyCreationException e) {
				return false;
//				e.printStackTrace();
			}
		}

		Set<OWLEntity> signature4StarModule = new HashSet<OWLEntity>();
		switch (moduleType){
		case BOT:
			signature4StarModule = new HashSet<OWLEntity>(classesWithGap);
			moduleSuffix += "-bot";
			break;
		case TOP:
			for (String p : predicatesWithGap)
				signature4StarModule.add(factory.getOWLClass(IRI.create(Utility.removeAngleBrackets(p))));
			moduleSuffix += "-top";
			break;
		case STAR:
			signature4StarModule = new HashSet<OWLEntity>(classesWithGap);
			for (String p : predicatesWithGap)
				signature4StarModule.add(factory.getOWLClass(IRI.create(Utility.removeAngleBrackets(p))));
			moduleSuffix += "-star";
			break;
		}

		try {
			SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(ontology.getOWLOntologyManager(), reducedOntology, moduleType);
			reducedOntology = extractor.extractAsOntology(signature4StarModule, IRI.create(ontology.getOWLOntologyManager().getOntologyDocumentIRI(ontology).toString().replace(".owl", moduleSuffix+".owl")));

			if (smallerEnoughToUpdateUpperProgram(currentOntologySize, reducedOntology.getAxiomCount())){
				program.updateUpperProgram(reducedOntology);
				Logger_MORe.logInfo("after refining the module, we have " + reducedOntology.getAxiomCount() + "axioms");
				return true;
			}

		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		return false;
	}

	protected boolean smallerEnoughToUpdateUpperProgram(int previousSize, int newSize){
		if (previousSize == 0)
			return false;
		return (((previousSize - newSize)*100)/previousSize > 25);
	}

	protected void updateUnsatisfiableClasses(){
		unsatisfiableClasses = new HashSet<OWLClass>();
		List<String> individuals4unsatClasses = new LinkedList<String>();
		String unsatQuery = "select ?x where { " +
				"?x " + MyPrefixes.PAGOdAPrefixes.expandText("rdf:type") + " " + MyPrefixes.PAGOdAPrefixes.expandText("owl:Nothing") + " }";
		TupleIterator iter = null;
		try{
			iter = lowerStore.getDataStore().compileQuery(unsatQuery);
			for (long multi = iter.open(); multi != 0; multi = iter.getNext()) {
				String s = RDFoxTripleManager.getRawTerm(iter.getResource(0));
				OWLClass c = indManager.getClass4Individual(s); 
				if (c != null){
					unsatisfiableClasses.add(c);
					individuals4unsatClasses.add(s);
				}
			}
		} catch (JRDFStoreException e){
			e.printStackTrace();
			if (iter != null) iter.dispose();
		}
		finally{
			if (iter != null) iter.dispose();
		}
		classesToClassify.removeAll(unsatisfiableClasses);
		classesWithGap = classesToClassify;
		indManager.registerFullyClassifiedClasses(individuals4unsatClasses);
		Logger_MORe.logInfo("found " + unsatisfiableClasses.size() + " unsatisfiable classes in the lower bound");
		Logger_MORe.logDebug(unsatisfiableClasses.toString());
	}


	protected OWLOntology getAxiomsToFinish() throws OWLOntologyCreationException{
		if (encoder == null){
			if (!program.getGeneral().isHorn() && multiStageTag)
				encoder = new TrackingRuleEncoderDisjVar14Classification(program.getUpper(), trackingStore);
			else
				encoder = new TrackingRuleEncoderWithGap4Classification(program.getUpper(), trackingStore);
		}

		MultiQueryTracker tracker = new MultiQueryTracker(encoder, lowerStore, new MultiQueryRecord(queryRecords));

		OWLOntology knowledgebase; 
		t.reset(); 

//				////
//				for (OWLAxiom ax : tracker.extract(trackingStore).getAxioms())
//					System.out.println(ax.toString());
				////

		knowledgebase = indManager.rewriteABoxAxiomsAsTBoxAxioms(tracker.extract(trackingStore));
//		Utility.printAllTriples(trackingStore.getDataStore());

		//		/////
		//		Utility.saveOntology(knowledgebase.getOWLOntologyManager(), knowledgebase, "file:/Users/Ana/Documents/Work/DatalogModules/MORe_2.0/smallOntology.owl");
		//		/////

		return knowledgebase;
	}


	public void evaluate(QueryRecord queryRecord) {
		Logger_MORe.logDebug(queryRecord.getQueryText());
		evaluateLower(queryRecord);
		evaluateUpper(queryRecord);
	}
	public void evaluateLower(QueryRecord queryRecord) {
		AnswerTuples answer = null;
		t.reset(); 
		try {
//			answer = lowerStore.evaluate(queryRecord.getQueryText(), queryRecord.getAnswerVariables());
			boolean expandEquality = ((QueryRecord4Classification) queryRecord).getQueryType() != ClassificationQueryType.INDIVIDUAL;
			answer = lowerStore.evaluate(queryRecord.getQueryText(), queryRecord.getAnswerVariables(), expandEquality);
			Logger_MORe.logTrace(t.duration());
			queryRecord.updateLowerBoundAnswers(answer);
		} finally {
			if (answer != null) answer.dispose();
		}
	}



	public void evaluateUpper(QueryRecord queryRecord){
		AnswerTuples answer = null;
		t.reset();
		try {
			if (queryRecord.isBottom() || !multiStageTag || (individualsWithContradictionsInLazyStore != null && !individualsWithContradictionsInLazyStore.isEmpty())){

//				answer = trackingStore.evaluate(queryRecord.getQueryText(), queryRecord.getAnswerVariables());
				boolean expandEquality = ((QueryRecord4Classification) queryRecord).getQueryType() != ClassificationQueryType.INDIVIDUAL;
				answer = trackingStore.evaluate(queryRecord.getQueryText(), queryRecord.getAnswerVariables(), expandEquality);
				Logger_MORe.logTrace(t.duration());

				if (!queryRecord.isBottom() && multiStageTag){
					Set<AnswerTuple> intersection = new HashSet<AnswerTuple>();
					AnswerTuples answerLazy = null;
					try{

						answerLazy = lazyUpperStore.evaluate(queryRecord.getQueryText(), queryRecord.getAnswerVariables());
						for (; answerLazy.isValid(); answerLazy.moveNext())
							intersection.add(answerLazy.getTuple());
						for (; answer.isValid(); answer.moveNext())
							if (individualsWithContradictionsInLazyStore.contains(answer.getTuple().getRawTerm(0)))
								intersection.add(answer.getTuple());
						queryRecord.updateUpperBoundAnswers(intersection);
					}
					finally{
						if (answerLazy != null) answer.dispose();
					}
				}
				else queryRecord.updateUpperBoundAnswers(answer);
			}
			else{//we only need to retrieve the upperAnswers from the lazyUpperStore
				answer = lazyUpperStore.evaluate(queryRecord.getQueryText(), queryRecord.getAnswerVariables());
				Logger_MORe.logTrace(t.duration());
				queryRecord.updateUpperBoundAnswers(answer);
			}
		} finally {
			if (answer != null) answer.dispose();
		}
	}

	
	public Set<OWLClass> getAllSuperClasses(OWLClass c){
		Set<OWLClass> ret = new HashSet<OWLClass>();
		OWLOntologyManager manager = ontology.getOWLOntologyManager();
		OWLDataFactory factory = manager.getOWLDataFactory();
		
		if (unsatisfiableClasses.contains(c)){
			ret.add(factory.getOWLNothing());
			return ret;
		}
		
		Individual i = indManager.getInstanceIndividual(c, false);
		if (i != null){
			String query = "select ?z where { " +
					i.toString() + " " + MyPrefixes.PAGOdAPrefixes.expandText("rdf:type") + " ?z }";
			QueryRecord queryRecord = getQueryManager().create(query);
			AnswerTuples answer = null;
			try {
				answer = lowerStore.evaluate(queryRecord.getQueryText(), queryRecord.getAnswerVariables());
				queryRecord.updateLowerBoundAnswers(answer);
			} finally {
				if (answer != null) answer.dispose();
			}

			for (AnswerTuple tuple : queryRecord.getSoundAnswerTuples()){
				OWLClass superClass = factory.getOWLClass(IRI.create(Utility.removeAngleBrackets(tuple.getRawTerm(0))));
				if (!superClass.equals(c))
					ret.add(superClass);
			}
		}
		return ret;
	}
	

	public Set<OWLClass> getPotentialSuperClasses(OWLClass c){
		Set<OWLClass> ret = new HashSet<OWLClass>();
		
		if ( c.isOWLNothing() || unsatisfiableClasses.contains(c)) return ret;
		
		OWLOntologyManager manager = ontology.getOWLOntologyManager();
		OWLDataFactory factory = manager.getOWLDataFactory();
		Individual i = indManager.getInstanceIndividual(c, false);
		if (i != null){
			String query = "select ?z where { " +
					i.toString() + " " + MyPrefixes.PAGOdAPrefixes.expandText("rdf:type") + " ?z }";
			QueryRecord queryRecord = getQueryManager().create(query);
			AnswerTuples answer = null;
			try {
				if (!multiStageTag || (individualsWithContradictionsInLazyStore != null && !individualsWithContradictionsInLazyStore.isEmpty())){
					answer = trackingStore.evaluate(queryRecord.getQueryText(), queryRecord.getAnswerVariables());

					if (multiStageTag){
						Set<AnswerTuple> intersection = new HashSet<AnswerTuple>();
						AnswerTuples answerLazy = null;
						try{

							answerLazy = lazyUpperStore.evaluate(queryRecord.getQueryText(), queryRecord.getAnswerVariables());
							for (; answerLazy.isValid(); answerLazy.moveNext())
								intersection.add(answerLazy.getTuple());
							for (; answer.isValid(); answer.moveNext())
								if (individualsWithContradictionsInLazyStore.contains(answer.getTuple().getRawTerm(0)))
									intersection.add(answer.getTuple());
							queryRecord.updateUpperBoundAnswers(intersection);
						}
						finally{
							if (answerLazy != null) answer.dispose();
						}
					}
					else queryRecord.updateUpperBoundAnswers(answer);
				}
				else{//we only need to retrieve the upperAnswers from the lazyUpperStore
					answer = lazyUpperStore.evaluate(queryRecord.getQueryText(), queryRecord.getAnswerVariables());
					Logger_MORe.logTrace(t.duration());
					queryRecord.updateUpperBoundAnswers(answer);
				}
			} finally {
				if (answer != null) answer.dispose();
			}

			for (AnswerTuple tuple : queryRecord.getGapAnswerTuples()){
				OWLClass superClass = factory.getOWLClass(IRI.create(Utility.removeAngleBrackets(tuple.getRawTerm(0))));
				ret.add(superClass);
			}
		}
		return ret;
	}
	
	
	public int getNundecidedSubsumptionPairs(){
		return nUndecidedSubsumptionPairs;
	}
	
	public Set<OWLClass> getUnsatisfiableClasses(){
		return unsatisfiableClasses;
	}
	
	public boolean fullyClassifies(OWLClass c){
		return !classesWithGap.contains(c);
	}
	
	public IndividualManager getIndividualManager(){
		return indManager;	
	}

	@Override
	public QueryManager getQueryManager(){
		return queryManager;
	}


	public void dispose(){
		if (encoder != null) encoder.dispose();
		if (lowerStore != null) lowerStore.dispose();
		if (lazyUpperStore != null) lazyUpperStore.dispose();
		if (trackingStore != null) trackingStore.dispose();
		//TODO what other things do I need to dispose and how?
	}

}
