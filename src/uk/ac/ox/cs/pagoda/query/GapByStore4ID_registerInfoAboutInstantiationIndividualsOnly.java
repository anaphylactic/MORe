package uk.ac.ox.cs.pagoda.query;

import java.io.File;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import org.semanticweb.more.pagoda.IndividualManager;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.more.util.Utility;

import uk.ac.ox.cs.JRDFox.JRDFStoreException;
import uk.ac.ox.cs.JRDFox.Prefixes;
import uk.ac.ox.cs.JRDFox.store.DataStore.UpdateType;
import uk.ac.ox.cs.pagoda.reasoner.light.BasicQueryEngine;
import uk.ac.ox.cs.pagoda.reasoner.light.RDFoxQueryEngine;
import uk.ac.ox.cs.pagoda.util.MyPrefixes;
import uk.ac.ox.cs.pagoda.util.Timer;

public class GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly extends GapByStore4ID {
	//in addition to adding annotated copies of ALL tuples in the gap, as superclass does,
	//registers info about which instantiation individuals are mentioned in unary facts in 
	//the gap, and which (unary) predicates are asserted about them  

	Set<String> namedIndividualsWithGap = new HashSet<String>();
	LinkedList<String> namedInstancesOfNothing = new LinkedList<String>();

	
	public GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly(
			BasicQueryEngine engine) {
		super(engine);
	}
	
	
	//exactly the same as compile(String) in superclass, only change is File rather than String
	public void compileFromFile(File programFile) throws JRDFStoreException {
		clear(); 

		boolean incrementally = true; 
		Timer t = new Timer();
		long oldTripleCount = m_store.getTriplesCount();
		
		if (programFile != null) {
			m_store.setNumberOfThreads(1);
			m_store.importFiles(new File[]{programFile}, new Prefixes(), UpdateType.Add, true);
			m_store.setNumberOfThreads(RDFoxQueryEngine.matNoOfThreads);
			Logger_MORe.logDebug("rules imported " + t.duration());
			incrementally = false; 
		}
		t.reset();
		m_store.applyReasoning(incrementally);
		Logger_MORe.logDebug(t.duration() + "to actually materialise!");

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
				
				boolean isRDFtype = isRDF_TYPE();
				if (isRDFtype) {
					predicate = getGapPredicateID(tuple[2]); 
					if (predicate == null) continue; 
					tuple[2] = predicate; 
				}
				else {
					predicate = getGapPredicateID(tuple[1]); 
					if (predicate == null) continue;  
					tuple[1] = predicate; 
				}
				if (isRDFtype)
					registerTuple();
				return true; 
			}
		} catch (JRDFStoreException e) {
			e.printStackTrace();
			return false; 
		}
		return false; 
	}

	
	protected void registerTuple(){
		String ind = tripleManager.getRawTerm(tuple[0]);
		if (IndividualManager.isInstantiationIndividual(ind) && !Utility.isInternalPredicate(currentPredicate)){
			predicatesWithGap.add(currentPredicate);
			namedIndividualsWithGap.add(ind);
			if (currentPredicate.contains(MyPrefixes.PAGOdAPrefixes.expandText("owl:Nothing")))
				namedInstancesOfNothing.add(ind);
		}
	}
	
	public void registerTuple(AnswerTuple tuple){//this method requires a triple, always 3 terms!
		if (tuple.getRawTerm(1).contains(MyPrefixes.PAGOdAPrefixes.expandText("rdf:type"))){
			String ind = tuple.getRawTerm(0);
			String pred = tuple.getRawTerm(2);
			if (IndividualManager.isInstantiationIndividual(ind) && !Utility.isInternalPredicate(pred)){
				predicatesWithGap.add(pred);
				namedIndividualsWithGap.add(ind);
				if (pred.contains(MyPrefixes.PAGOdAPrefixes.expandText("owl:Nothing")))
					namedInstancesOfNothing.add(ind);
			}	
		}
	}
	
	String currentPredicate;
	
	protected Long getGapPredicateID(long originalID) {
		String originalPredicate = tripleManager.getRawTerm(originalID);
		if (isAuxPredicate(originalPredicate)) {
			currentPredicate = null;
			return null; 
		}
		currentPredicate = originalPredicate;
		Long gapID = original2gap.get(originalID);
		if (gapID == null){
			String gapPredicate = prefixes.expandIRI(getGapPredicate(originalPredicate));
			gapID = tripleManager.getResourceID(gapPredicate);
			original2gap.put(originalID, gapID); 
		}
		return gapID;
	}
	
	public void registerGapTuples() throws JRDFStoreException { 
		//instead of addBackTo when working in the multistage store to register info about the gap for instantiation individuals 
		//without adding gap tuples to the store  
		Timer t = new Timer(); 
		while (hasNext()) {
			next(); //no need to do anything else here, the gap information is processed inside method hasNext();
		}
		Logger_MORe.logDebug("current store finished registering predicates and named constants in gap tuples in " + t.duration() + "."); 
	}
	public Set<String> getNamedIndividualsWithGap() {
		return namedIndividualsWithGap; 
	}
	public LinkedList<String> getNamedInstancesOfNothing() {
		return namedInstancesOfNothing; 
	}
	
}
