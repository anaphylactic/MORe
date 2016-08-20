package uk.ac.ox.cs.pagoda.reasoner.light;

import java.io.File;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.more.pagoda.IndividualManager;
import org.semanticweb.more.pagoda.rules.DatalogProgram4Classification;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.more.util.Utility;

import uk.ac.ox.cs.JRDFox.JRDFStoreException;
import uk.ac.ox.cs.JRDFox.Prefixes;
import uk.ac.ox.cs.JRDFox.model.GroundTerm;
import uk.ac.ox.cs.JRDFox.store.DataStore;
import uk.ac.ox.cs.JRDFox.store.DataStore.UpdateType;
import uk.ac.ox.cs.JRDFox.store.Parameters;
import uk.ac.ox.cs.JRDFox.store.TripleStatus;
import uk.ac.ox.cs.JRDFox.store.TupleIterator;
import uk.ac.ox.cs.pagoda.hermit.DLClauseHelper;
import uk.ac.ox.cs.pagoda.owl.OWLHelper;
import uk.ac.ox.cs.pagoda.query.AnswerTuples;
import uk.ac.ox.cs.pagoda.query.GapByStore4ID;
import uk.ac.ox.cs.pagoda.query.GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly;
import uk.ac.ox.cs.pagoda.rules.DatalogProgram;
import uk.ac.ox.cs.pagoda.rules.Program;
import uk.ac.ox.cs.pagoda.util.ConjunctiveQueryHelper;
import uk.ac.ox.cs.pagoda.util.MyPrefixes;
import uk.ac.ox.cs.pagoda.util.Namespace;
import uk.ac.ox.cs.pagoda.util.Timer;
import uk.ac.ox.cs.pagoda.util.UFS;
import uk.ac.ox.cs.pagoda.util.Utility_PAGOdA;

public class BasicQueryEngine extends RDFoxQueryEngine {

	protected DataStore store; 
	protected Parameters parameters = new Parameters(); 
	
	public BasicQueryEngine(String name) {
		super(name); 
		store = RDFoxQueryEngine.createDataStore();
	}

	public void materialiseFoldedly(DatalogProgram dProgram, GapByStore4ID gap) {
		materialise("lower program", new File(dProgram.getLower().getOutputPath()));
		try {
			((GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly) gap).compileFromFile(new File(dProgram.getUpper().getOutputPath()));
			gap.addBackTo();
			getDataStore().clearRulesAndMakeFactsExplicit();
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		} finally {
			gap.clear(); 
		}
	}
	
	public int materialiseRestrictedly(DatalogProgram dProgram, GapByStore4ID gap) {
		if (gap != null) {
			materialise("lower program", new File(dProgram.getLower().getOutputPath()));
			try {
				((GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly) gap).compileFromFile(new File(dProgram.getUpper().getOutputPath()));
				gap.addBackTo();
				getDataStore().clearRulesAndMakeFactsExplicit();
			} catch (JRDFStoreException e) {
				e.printStackTrace();
			} finally {
				gap.clear(); 
			}
		}
		else 
			materialise("upper program", new File(dProgram.getUpper().getOutputPath()));
		
		return 1; 
	}
	
	@Override
	public AnswerTuples evaluate(String queryText) {
		return evaluate(queryText, ConjunctiveQueryHelper.getAnswerVariables(queryText)); 
	}
	
	@Override
	public AnswerTuples evaluate(String queryText, String[] answerVars) {
		TupleIterator tupleIterator;
		try {
			tupleIterator = store.compileQuery(queryText, MyPrefixes.PAGOdAPrefixes.getRDFoxPrefixes(), parameters);
		} catch (JRDFStoreException e) {
			e.printStackTrace();
			return null; 
		}
		return new RDFoxAnswerTuples(answerVars, tupleIterator); 
	}
	//byAna
	public AnswerTuples evaluate(String queryText, String[] answerVars, boolean expandEquality) {
		TupleIterator tupleIterator;
		boolean originalValue = parameters.m_expandEquality;
		setExpandEquality(expandEquality);
		try {
			tupleIterator = store.compileQuery(queryText, MyPrefixes.PAGOdAPrefixes.getRDFoxPrefixes(), parameters);
		} catch (JRDFStoreException e) {
			e.printStackTrace();
			setExpandEquality(originalValue);
			return null; 
		}
		setExpandEquality(originalValue);
		return new RDFoxAnswerTuples(answerVars, tupleIterator); 
	}

	@Override
	public DataStore getDataStore() {
		return store;
	}

	@Override
	public Parameters getParameters() {
		return parameters;
	}

	@Override
	public void dispose() {
		store.dispose();		
	}

	protected void outputClassAssertions(String filename) {
		TupleIterator allTuples = null;
		boolean redirect = false; 
		try {
			allTuples = getDataStore().compileQuery("SELECT ?X ?Z WHERE { ?X <" + Namespace.RDF_TYPE + "> ?Z }", prefixes, getParameters());
			redirect = Utility_PAGOdA.redirectCurrentOut(filename);
			for (long multi = allTuples.open(); multi != 0; multi = allTuples.getNext()) 
				System.out.println(RDFoxTripleManager.getRawTerm(allTuples.getResource(0)) + " " + RDFoxTripleManager.getRawTerm(allTuples.getResource(1))); 
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		} finally {
			if (redirect) Utility_PAGOdA.closeCurrentOut();
			if (allTuples != null) allTuples.dispose();
		}
	}
	
	public void outputInstance4BinaryPredicate(String iri, String filename) {
		Utility_PAGOdA.redirectCurrentOut(filename);
		outputInstance4BinaryPredicate(iri);
		Utility_PAGOdA.closeCurrentOut();
	}
	
	public void outputInstance4BinaryPredicate(String iri) {
		outputAnswers("select ?x ?y where { ?x <" + iri + "> ?y . }");
	}
	
	public void outputInstanceNumbers(String filename) {
		TupleIterator predicateTuples = null;
		TupleIterator instanceTuples; 
		Set<String> number = new HashSet<String>(); 
		String predicate; 
		try {
			predicateTuples = getDataStore().compileQuery("SELECT DISTINCT ?Y WHERE { ?X <" + Namespace.RDF_TYPE + "> ?Y }", prefixes, getParameters());
			for (long multi = predicateTuples.open(); multi != 0; multi = predicateTuples.getNext()) {
				predicate = RDFoxTripleManager.getRawTerm(predicateTuples.getResource(0));
				instanceTuples = null; 
				try {
					instanceTuples = getDataStore().compileQuery("SELECT ?X WHERE { ?X <" + Namespace.RDF_TYPE + "> " + predicate + " }", prefixes, getParameters());
					long totalCount = 0; 
					for (long multi1 = instanceTuples.open(); multi1 != 0; multi1 = instanceTuples.getNext()) {
						totalCount += instanceTuples.getMultiplicity();
					}
					number.add(predicate + " * " + totalCount);
				} finally {
					if (instanceTuples != null) instanceTuples.dispose(); 
				}
			}
			
			predicateTuples.dispose();
			
			predicateTuples = getDataStore().compileQuery("SELECT DISTINCT ?Y WHERE { ?X ?Y ?Z }", MyPrefixes.PAGOdAPrefixes.getRDFoxPrefixes(), getParameters());
			for (long multi = predicateTuples.open(); multi != 0; multi = predicateTuples.getNext()) {
				predicate = RDFoxTripleManager.getRawTerm(predicateTuples.getResource(0)); 
				instanceTuples = null; 
				try {
					instanceTuples = getDataStore().compileQuery("SELECT ?X ?Z WHERE { ?X " + predicate + " ?Z }", MyPrefixes.PAGOdAPrefixes.getRDFoxPrefixes(), getParameters());
					;
					long totalCount = 0; 
					for (long multi1 = instanceTuples.open(); multi1 != 0; multi1 = instanceTuples.getNext())
						totalCount += instanceTuples.getMultiplicity();
					number.add(predicate + " * " + totalCount); 
				} finally {
					if (instanceTuples != null) instanceTuples.dispose(); 
				}
			}
			
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		} finally {
			if (predicateTuples != null) predicateTuples.dispose();
		}
		
		Utility_PAGOdA.redirectCurrentOut(filename);
		String[] ordered = number.toArray(new String[0]);
		Arrays.sort(ordered, new DLPredicateComparator());
		for (String line: ordered) System.out.println(line); 
		Utility_PAGOdA.closeCurrentOut();
		
	}
	
	public TupleIterator internal_evaluateAgainstIDBs(String queryText) throws JRDFStoreException {
		TupleIterator iter = store.compileQuery(queryText, MyPrefixes.PAGOdAPrefixes.getRDFoxPrefixes(), parameters, TripleStatus.TUPLE_STATUS_IDB.union(TripleStatus.TUPLE_STATUS_EDB.union(TripleStatus.TUPLE_STATUS_IDB_MERGED)), TripleStatus.TUPLE_STATUS_IDB);
		iter.open();
		return iter; 
	}

	public TupleIterator internal_evaluate(String queryText) throws JRDFStoreException {
		TupleIterator iter = store.compileQuery(queryText, MyPrefixes.PAGOdAPrefixes.getRDFoxPrefixes(), parameters);
		iter.open(); 
		return iter; 
	}
	
	public void setExpandEquality(boolean flag) {
		parameters.m_expandEquality = flag; 
	}
	
	public TupleIterator internal_evaluateNotExpanded(String queryText) throws JRDFStoreException {
		parameters.m_expandEquality = false; 
		TupleIterator iter = store.compileQuery(queryText, MyPrefixes.PAGOdAPrefixes.getRDFoxPrefixes(), parameters); 
		iter.open(); 
		parameters.m_expandEquality = true; 
		return iter;
	}

	
	public TupleIterator internal_evaluate(String queryText, boolean incrementally) throws JRDFStoreException {
		return incrementally ? internal_evaluateAgainstIDBs(queryText) : internal_evaluate(queryText);
	}

	Set<DLClause> materialisedRules = new HashSet<DLClause>(); 
	
	public String getUnusedRules(Collection<DLClause> clauses, boolean toUpdate) {
		DLClause clause;
		for (Iterator<DLClause> iter = clauses.iterator(); iter.hasNext(); ) {
			if (materialisedRules.contains(clause = iter.next()))
				iter.remove();
			else if (toUpdate) materialisedRules.add(clause); 
		}
		
		if (clauses.isEmpty()) return null;
		
		return Program.toString(clauses);
	}

	public void outputMaterialisedRules() {
		System.out.println(DLClauseHelper.toString(materialisedRules));		
	}

	public void outputAnswers(String query) {
		TupleIterator iter = null;
		try {
			iter = internal_evaluate(query);
			System.out.println(query); 
			int arity = iter.getArity(); 
			for (long multi = iter.open(); multi != 0; multi = iter.getNext())  {
				for (int i = 0; i < arity; ++i)
					System.out.print(RDFoxTripleManager.getRawTerm(iter.getResource(i)) + "\t");
				System.out.println(); 
			}
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		} finally {
			if (iter != null) iter.dispose(); 
		}
	}

	public void outputInstance4UnaryPredicate(String iri) {
		outputAnswers("select ?x where { ?x "
					+ "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <"
					+ iri 
					+ "> .}"); 
	}

	public void outputSubjects(String p, String o) {
		outputAnswers("select x where { ?x <" + p + "> <" + o + "> . }");
	}

	public void outputObjects(String s, String p) {
		outputAnswers("select ?x where { <" + s + "> <" + p + "> ?x . }");
	}

	public void outputIDBFacts() {
		TupleIterator iter = null; 
		try {
			iter = internal_evaluateAgainstIDBs("select distict ?x ?y ?z where { ?x ?y ?z }");
			for (long multi = iter.open(); multi != 0; multi = iter.getNext()) {
				for (int i = 0; i < 3; ++i)
					System.out.print(RDFoxTripleManager.getRawTerm(iter.getResource(i)) + "\t"); 
				System.out.println(); 
			}
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		} finally {
			if (iter != null) iter.dispose();
		}
		
	}
	
	public void outputType4Individual(String iri) {
		outputAnswers("select ?z where { <" + iri + "> " + Namespace.RDF_TYPE_QUOTED + " ?z }");
	}
	
	public int getSameAsNumber() {
		TupleIterator iter = null; 
		int counter = 0; 
		try {
			iter = internal_evaluate("select ?x ?y where {?x " + Namespace.EQUALITY_QUOTED + " ?y . }");
			for (long multi = iter.open(); multi != 0; multi = iter.getNext()) 
				if (iter.getResourceID(0) != iter.getResourceID(1))
					++counter;
		} catch (JRDFStoreException e) {
			e.printStackTrace(); 
		} finally {
			if (iter != null) iter.dispose();
		}
		return counter; 
	}
	
	private UFS<String> equalityGroups = null; 
	
	public UFS<String> getEqualityGroups(boolean reuse) {
		if (reuse && equalityGroups != null) return equalityGroups; 

		equalityGroups = new UFS<String>(); 
		
		TupleIterator answers = null; 
		try {
			Timer t = new Timer(); 
			answers = internal_evaluate("select ?x ?z  where {?x " + Namespace.EQUALITY_QUOTED + "?z . }");
			for (long multi = answers.open(); multi != 0; multi = answers.getNext()) {
				if (answers.getResourceID(0) != answers.getResourceID(1))
					equalityGroups.merge(answers.getResource(0).m_lexicalForm, answers.getResource(1).m_lexicalForm); 
			}
			Logger_MORe.logInfo("@Time to group individuals by equality: " + t.duration());
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		} finally {
			if (answers != null) answers.dispose(); 
		}

		return equalityGroups; 
	}

	public void clearRulesAndIDBFacts(Collection<long[]> collection) {
//		performDeletion(collection); 
		collection.clear();
		try {
			store.clearRulesAndMakeFactsExplicit();
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		}
	}

	@SuppressWarnings("unused")
	private void performDeletion(Collection<long[]> collection) {
		Logger_MORe.logInfo("Remove all rules, idb facts and added staff...");
		Timer timer = new Timer();  
		TupleIterator iter = null;
		try {
			UpdateType ut = UpdateType.ScheduleForDeletion; 
			for (long[] t: collection) 
				store.addTriplesByResourceIDs(t, ut);
			
			iter = internal_evaluateAgainstIDBs("select ?x ?y ?z where { ?x ?y ?z . }");
			for (long multi = iter.open(); multi != 0; multi = iter.getNext()) {
				long[] triple = new long[3];
				for (int i = 0; i < 3; ++i)
					triple[i] = iter.getResourceID(i); 
				store.addTriplesByResourceIDs(triple, ut);
			}
			store.applyReasoning(true);
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		} finally {
			if (iter != null) iter.dispose();
		}
		Logger_MORe.logInfo("Time for deletion: " + timer.duration()); 
	}


	
	
	
	//methods added by Ana
	@Override
	public void materialise(String programName, File programFile) {//changed String programText argument to File programFile
		materialise(programName,programFile, true);
	}
	
	public void materialise(String programName, File programFile, boolean clearRules) {
		if (programFile == null) return ; 
		Timer t = new Timer();
		DataStore store = getDataStore(); 
		try {
			long oldTripleCount = store.getTriplesCount(), tripleCount;
			store.setNumberOfThreads(1);
			store.importFiles(new File[]{programFile}, new Prefixes(), UpdateType.Add, true);
			store.setNumberOfThreads(RDFoxQueryEngine.matNoOfThreads);
			
			store.applyReasoning();
			tripleCount = store.getTriplesCount(); 
			Logger_MORe.logDebug(name + " store after materialising " + programName + ": " + tripleCount + " (" + (tripleCount - oldTripleCount) + " new)");
			if (clearRules)
				store.clearRulesAndMakeFactsExplicit();
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		}
		Logger_MORe.logDebug(name + " store finished the materialisation of " + programName + " in " + t.duration() + " seconds.");
	}
	
	
	
	
	public void materialise(DatalogProgram4Classification dProgram, String skolemDataFileName, GapByStore4ID gap, BasicQueryEngine lowerStore, IndividualManager indManager) {
		addExtraTriplesFromLowerStore(lowerStore, indManager);
		importRDFData("Skolem data", skolemDataFileName);
		
//		Utility.exportStore(store,"output/storeBeforeUpperMaterialisation.ttl");
		
//		String program = dProgram.getUpper().toString();
		try {
			((GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly) gap).compileFromFile(new File(dProgram.getUpper().getOutputPath()));
			gap.addBackTo();
			getDataStore().clearRulesAndMakeFactsExplicit();
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		} finally {
			gap.clear(); 
		}
	}
	
	protected void addExtraTriplesFromLowerStore(BasicQueryEngine lowerStore, IndividualManager indManager){
		Logger_MORe.logInfo("adding triples from the lower store");
		int counter = 0;
		long t = System.currentTimeMillis();
		for (String unaryPred : getPresentPredicates(lowerStore)){
			TupleIterator derivedTuples = null;
			try {
//				derivedTuples = lowerStore.internal_evaluateAgainstIDBs("select distinct ?x where { ?x <"
//						+ Namespace.RDF_TYPE + "> " + unaryPred + " . }");
				derivedTuples = lowerStore.internal_evaluate("select distinct ?x where { ?x <"
						+ Namespace.RDF_TYPE + "> " + unaryPred + " . }");
				for (long multi = derivedTuples.open(); multi != 0; multi = derivedTuples.getNext()) {
					String i = RDFoxTripleManager.getRawTerm(derivedTuples.getResource(0));
					if (indManager.isIndividual4ClassToClassify(i)){
						//TODO consider doing this by ID instead of adding the triples directly
//						RDFoxTripleManager tripleManager = new RDFoxTripleManager(getDataStore(), false);
						GroundTerm[] triple = new GroundTerm[] {
								uk.ac.ox.cs.JRDFox.model.Individual.create(OWLHelper.removeAngles(i)),//do I need to remove < > ? 
								uk.ac.ox.cs.JRDFox.model.Individual.RDF_TYPE, 
								uk.ac.ox.cs.JRDFox.model.Individual.create(OWLHelper.removeAngles(unaryPred)) };
						getDataStore().addTriples(triple, UpdateType.Add);
						
						counter++;
					}
				}
			} catch (JRDFStoreException e) {
				e.printStackTrace();
			} finally {
				if (derivedTuples != null) derivedTuples.dispose();
			}
		}
	}
	
	protected Set<String> getPresentPredicates(BasicQueryEngine store) { //copied from QueryTracker
		Timer t = new Timer();
		Set<String> unaryPredicates = new HashSet<String>();
		TupleIterator derivedTuples = null;
		try {
			derivedTuples = store.internal_evaluate("select distinct ?z where { ?x <"
					+ Namespace.RDF_TYPE + "> ?z . }");
			for (long multi = derivedTuples.open(); multi != 0; multi = derivedTuples.getNext()) {
				String p = RDFoxTripleManager.getRawTerm(derivedTuples.getResource(0));
				if (!Utility.isRDFoxInternalPredicate(p) && !Utility.isHermiTInternalPredicate(p))
					unaryPredicates.add(p);
			}
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		} finally {
			if (derivedTuples != null)
				derivedTuples.dispose();
		}
		Logger_MORe.logDebug(t.duration() + " to find derived predicates");
		return unaryPredicates;
	}
	
	protected Set<String> getDerivedPredicates(BasicQueryEngine store) { //copied from QueryTracker
		Timer t = new Timer();
		Set<String> unaryPredicates = new HashSet<String>();
		TupleIterator derivedTuples = null;
		try {
			derivedTuples = store.internal_evaluateAgainstIDBs("select distinct ?z where { ?x <"
					+ Namespace.RDF_TYPE + "> ?z . }");
			for (long multi = derivedTuples.open(); multi != 0; multi = derivedTuples.getNext()) {
				String p = RDFoxTripleManager.getRawTerm(derivedTuples.getResource(0));
				if (!Utility.isRDFoxInternalPredicate(p))
					unaryPredicates.add(p);
			}
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		} finally {
			if (derivedTuples != null)
				derivedTuples.dispose();
		}
		Logger_MORe.logDebug(t.duration() + " to find derived predicates");
		return unaryPredicates;
	}
}
