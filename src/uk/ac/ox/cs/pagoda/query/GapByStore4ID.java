package uk.ac.ox.cs.pagoda.query;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.semanticweb.more.util.Logger_MORe;

import uk.ac.ox.cs.JRDFox.JRDFStoreException;
import uk.ac.ox.cs.JRDFox.Prefixes;
import uk.ac.ox.cs.JRDFox.store.DataStore;
import uk.ac.ox.cs.JRDFox.store.DataStore.UpdateType;
import uk.ac.ox.cs.JRDFox.store.TupleIterator;
import uk.ac.ox.cs.pagoda.reasoner.light.BasicQueryEngine;
import uk.ac.ox.cs.pagoda.reasoner.light.RDFoxQueryEngine;
import uk.ac.ox.cs.pagoda.reasoner.light.RDFoxTripleManager;
import uk.ac.ox.cs.pagoda.util.MyPrefixes;
import uk.ac.ox.cs.pagoda.util.Namespace;
import uk.ac.ox.cs.pagoda.util.Timer;
//import uk.ac.ox.cs.pagoda.multistage.AnswerTupleID;

//public class GapByStore4ID extends GapTupleIterator<AnswerTupleID> {
public class GapByStore4ID extends GapTupleIterator<long[]> {

	protected MyPrefixes prefixes = MyPrefixes.PAGOdAPrefixes; 
	protected TupleIterator iterator = null; 
	
//	AnswerTupleID tuple;
	protected long[] tuple; 
	protected BasicQueryEngine m_engine; 
	protected DataStore m_store;
	protected RDFoxTripleManager tripleManager; 
	
	public GapByStore4ID(BasicQueryEngine engine) {
		m_engine = engine; 
		m_store = engine.getDataStore(); 
		tripleManager = new RDFoxTripleManager(m_store, false); 
	}
	
	protected long multi; 
	
	@Override
	public void compile(String program) throws JRDFStoreException {
		clear(); 

		boolean incrementally = true; 
		Timer t = new Timer();
		long oldTripleCount = m_store.getTriplesCount();
		
		if (program != null) {
//			m_store.importRules(program, UpdateType.Add, true, new Prefixes());			
			m_store.setNumberOfThreads(1);
			m_store.importText(program, new Prefixes(), UpdateType.Add, true);
			m_store.setNumberOfThreads(RDFoxQueryEngine.matNoOfThreads);
			Logger_MORe.logDebug("rules imported " + t.duration());
			incrementally = false; 
		}
//		else{
//		m_store.setNumberOfThreads(1);
//		Logger_MORe.logDebug("number of threads in store set to 1");
//	}
		t.reset();
		m_store.applyReasoning(incrementally);
		Logger_MORe.logDebug(t.duration() + "to actually materialise!");

//	m_store.setNumberOfThreads(RDFoxQueryEngine.matNoOfThreads);
//	Logger_MORe.logDebug("number of threads in store reset to " + RDFoxQueryEngine.matNoOfThreads);
		
		long tripleCount = m_store.getTriplesCount();
			
		Logger_MORe.logDebug("current store after materialising upper related rules: " + tripleCount + " (" + (tripleCount - oldTripleCount) + " new)", 
				"current store finished the materialisation of upper related rules in " + t.duration() + " seconds.");
		
		t.reset();
		m_engine.setExpandEquality(false);
		iterator = m_engine.internal_evaluateAgainstIDBs("select ?x ?y ?z where { ?x ?y ?z . }");
		m_engine.setExpandEquality(true);
		
		multi = iterator.open();
		Logger_MORe.logDebug("gap query evaluated ...");
		Logger_MORe.logDebug(t.duration());
	}
	
	@Override
	public boolean hasNext() {
		if (iterator == null) return false; 
		try {
			tuple = new long[3]; 
			Long predicate; 
			for (; multi != 0; multi = iterator.getNext()) {
				for (int i = 0; i < 3; ++i)
					tuple[i] = (int) iterator.getResourceID(i); 
				
				if (isRDF_TYPE()) {
					predicate = getGapPredicateID(tuple[2]); 
					if (predicate == null) continue; 
					tuple[2] = predicate; 
				}
				else {
					predicate = getGapPredicateID(tuple[1]); 
					if (predicate == null) continue;  
					tuple[1] = predicate; 
				}
				return true; 
			}
		} catch (JRDFStoreException e) {
			e.printStackTrace();
			return false; 
		}
		return false; 
	}
	
	@Override
//	public AnswerTupleID next() {
	public long[] next() {
		try {
			multi = iterator.getNext();
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		} 
		
		return tuple; 
	}
	
	Map<Long, Long> original2gap = new HashMap<Long, Long>();
//	LinkedList<String> predicatesWithGap = new LinkedList<String>();
	Set<String> predicatesWithGap = new HashSet<String>();//i want this to be a set!
	
	
//	public LinkedList<String> getPredicatesWithGap() {
	public Set<String> getPredicatesWithGap() {
		return predicatesWithGap; 
	}
	
	protected Long getGapPredicateID(long originalID) {
		Long gapID; 
		if ((gapID = original2gap.get(originalID)) != null) 
			return gapID;
		
		String originalPredicate = tripleManager.getRawTerm(originalID);
		if (isAuxPredicate(originalPredicate)) {
//			Utility.LOGS.info(originalPredicate); 
			return null; 
		}

		predicatesWithGap.add(originalPredicate);  
		String gapPredicate = prefixes.expandIRI(getGapPredicate(originalPredicate));
		gapID = tripleManager.getResourceID(gapPredicate);
		original2gap.put(originalID, gapID); 
		
		return gapID;
	}

	protected boolean isAuxPredicate(String originalPredicate) {
		if (originalPredicate.equals(Namespace.EQUALITY_QUOTED) || originalPredicate.equals("<" + Namespace.OWL_NS + "Nothing>")) return false;
		return originalPredicate.contains("_AUX") || originalPredicate.startsWith("<" + Namespace.OWL_NS);
	}

	protected boolean isRDF_TYPE() {
//		return tripleManager.isRdfTypeID(tuple.getTerm(1)); 
		return tripleManager.isRdfTypeID(tuple[1]); 
	}

	@Override
	public void remove() {
		Logger_MORe.logError("Unsupported operation!"); 
	}
	

	@Override
	public void save(String file) {
		Logger_MORe.logError("Unsupported Operation..."); 
	}
	
	@Override
	public void addBackTo() throws JRDFStoreException { 
		int tupleCounter = 0;
		Timer t = new Timer(); 
		long oldTripleCounter; 
		Logger_MORe.logDebug("current store before importing gap tuples: " + (oldTripleCounter = m_store.getTriplesCount())); 
		while (hasNext()) {
			next(); 
			++tupleCounter;
			tripleManager.addTripleByID(tuple);
		}

		long tripleCounter = m_store.getTriplesCount(); 
		Logger_MORe.logDebug("There are " + tupleCounter + " tuples in the gap between lower and upper bound materialisation.", 
				"current store after importing gap tuples: " + tripleCounter + " (" + (tripleCounter - oldTripleCounter) + ").", 
				"current store finished importing gap tuples: " + tripleCounter + " in " + t.duration() + "."); 
	}
	
	public void clear() {
		if (iterator != null) {
			iterator.dispose();
			iterator = null; 
		}
	}
		

	@Override
	public void addTo(DataStore store) throws JRDFStoreException {
		Logger_MORe.logError("Unsupported Operation..."); 
	}
}
