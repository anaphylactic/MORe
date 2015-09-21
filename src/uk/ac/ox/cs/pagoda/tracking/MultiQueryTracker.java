package uk.ac.ox.cs.pagoda.tracking;
import java.io.File;
import java.util.HashSet;
import java.util.Set;

import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;

import uk.ac.ox.cs.JRDFox.JRDFStoreException;
import uk.ac.ox.cs.JRDFox.Prefixes;
import uk.ac.ox.cs.JRDFox.store.DataStore;
import uk.ac.ox.cs.JRDFox.store.DataStore.UpdateType;
import uk.ac.ox.cs.JRDFox.store.TupleIterator;
import uk.ac.ox.cs.pagoda.hermit.DLClauseHelper;
import uk.ac.ox.cs.pagoda.query.MultiQueryRecord;
import uk.ac.ox.cs.pagoda.reasoner.light.BasicQueryEngine;
import uk.ac.ox.cs.pagoda.reasoner.light.RDFoxQueryEngine;
import uk.ac.ox.cs.pagoda.reasoner.light.RDFoxTripleManager;
import uk.ac.ox.cs.pagoda.util.MyPrefixes;
import uk.ac.ox.cs.pagoda.util.Timer;


public class MultiQueryTracker extends QueryTracker {

	
	protected MultiQueryRecord m_multiRecord;
	
	
	public MultiQueryTracker(TrackingRuleEncoder encoder,
			BasicQueryEngine lowerStore, MultiQueryRecord multiRecord){//Collection<QueryRecord> queryRecords) {
		super(encoder, lowerStore, null);

		try{
			if (!(encoder instanceof TrackingRuleEncoder4Classification))
				throw new IllegalArgumentException("we need a TrackingRuleEncoder4Classification here!");
		}
		catch (IllegalArgumentException e){
			e.printStackTrace();
		}
		m_multiRecord = multiRecord;
		m_manager = m_encoder.getOntology().getOWLOntologyManager();
	}
	
	
	public OWLOntology extract(BasicQueryEngine trackingStore) {
		//TODO clean up this method a bit
		try {
			if (m_multiRecord.getRelevantOntology() != null) {
				m_manager.removeOntology(m_multiRecord.getRelevantOntology());
				m_multiRecord.setRelevantOntology(null);
				m_multiRecord.clearClauses();
			}
			m_multiRecord.setRelevantOntology(m_manager.createOntology());
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		
		// m_encoder.saveTrackingRules("tracking_query" + m_record.getQueryID() + ".dlog");

		DataStore store = trackingStore.getDataStore();
		long oldTripleCount, tripleCount;
		try {
			Timer t1 = new Timer();
			oldTripleCount = store.getTriplesCount();
			
//			Iterator<QueryRecord> iter = m_multiRecord.getIndividualQueryRecords().iterator();
//			//look for a bottom query in the iter, if there is one
//			//setting the trackingRuleEncoder's current query to be a bottom query - if there is one - will make it encode rules for tracking without the optimisation for disjunctive rules, as is 
//			//needed for the tracking to be complete for the bottom predicates
//			if (iter.hasNext()){
//				boolean done = false;
//				while (iter.hasNext() && !done){
//					QueryRecord record = iter.next();
////					if (record.isBottom() || !iter.hasNext()){
//					if (!record.isBottom() || !iter.hasNext()){
//						m_encoder.setCurrentQuery(record);//TODO I don't want to have to do this! I din't really need to assign a query to the encoder
//						done = true;						
//						//////
//						System.out.println("current query set as " + record.getQueryText());
//						//////
//					}
//				}
//			}
			if (m_multiRecord.getIndividualQueryRecords().isEmpty())
				return m_multiRecord.getRelevantOntology();

			Logger_MORe.logDebug("encoder is an instance of " + m_encoder.getClass().toString());
			
//			for (QueryRecord record : m_multiRecord.getIndividualQueryRecords()){//TODO There should also be a more elegant way of doing this
//				((TrackingRuleEncoder4Classification) m_encoder).encodingClassificationQueries(record);
//			}
			((TrackingRuleEncoder4Classification) m_encoder).encodeClassificationQueries(m_multiRecord);
			Logger_MORe.logInfo("finished encoding rules and data for queries");
			
			
//			store.importRules(m_encoder.getTrackingProgram(), UpdateType.Add, true, new Prefixes());
			store.setNumberOfThreads(1);
//			Logger_MORe.logDebug("changed noThreads to 1 before loading tracking rules");
			store.importFiles(new File[]{new File(((TrackingRuleEncoder4Classification) m_encoder).getTrackingProgramOutputPath())}, new Prefixes(), UpdateType.Add, true);
			
//			Utility.exportStore(store,Utility_PAGOdA.TempDirectory + "storeBeforeTracking_expandedEq.ttl", true);
//			Utility.exportStore(store,Utility_PAGOdA.TempDirectory + "/storeBeforeTracking.ttl", false);
//			store.save(new File(Utility_PAGOdA.TempDirectory + "/savedStore.fmt"));
			
//			Logger_MORe.logDebug("finished adding rules to tracking store");
			
			store.setNumberOfThreads(RDFoxQueryEngine.matNoOfThreads);
			
//			Logger_MORe.logDebug("changed noThreads back to " + RDFoxQueryEngine.matNoOfThreads + " after loading tracking rules");
			Logger_MORe.logDebug("finished adding rules to tracking store");
			
			
			store.applyReasoning();			
			tripleCount = store.getTriplesCount();

			Logger_MORe.logDebug("tracking store after materialising tracking program: "
					+ tripleCount
					+ " ("
					+ (tripleCount - oldTripleCount)
					+ " new)");
			Logger_MORe.logDebug("tracking store finished the materialisation of tracking program in "
					+ t1.duration() + " seconds.");
			
//			Utility.printAllTriples(store);
			
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		}

		extractAxioms(trackingStore);

		try {
			store.clearRulesAndMakeFactsExplicit();
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		}

		return m_multiRecord.getRelevantOntology();
	}

	public void extractAxioms(BasicQueryEngine trackingStore) {
		Timer t = new Timer();
		Set<String> unaryPredicates = new HashSet<String>();
		Set<String> binaryPredicates = new HashSet<String>();

		getDerivedPredicates(trackingStore, unaryPredicates, binaryPredicates);

		/**
		 * To add all the relevant ABox assertions to the fragment
		 */

		int aboxAxiomCounter = extractUnaryTuples(trackingStore, m_manager.getOWLDataFactory(), unaryPredicates);
		//this method will take care of adding all necessary assertions to the relevant ontology of the multiQueryRecord 
//			+ extractBinaryTuples(trackingStore, m_manager.getOWLDataFactory(), binaryPredicates);
//			we do not need the binary tuples, there won't be any that are not in the gap - even if they are in the lowerStore, the will be mentioning anonymous individuals and we don't want them
		Logger_MORe.logInfo(aboxAxiomCounter + " ABox axioms added to the relevant ontology");
		
		/**
		 * To add all the relevant TBox rules to the fragment
		 */
		String queryText = m_encoder.getSelectedSPARQLQuery();

		DLClause clause;
		m_tBoxAxioms = new HashSet<OWLAxiom>();
		OWLAxiom tBoxAxiom;
		TupleIterator answers = null;
		String answer;
		try {
			answers = trackingStore.internal_evaluate(queryText);
			for (long multi = answers.open(); multi != 0; multi = answers.getNext()) {
				answer = RDFoxTripleManager.getRawTerm(answers.getResource(0));
				clause = m_encoder.getSelectedClause(MyPrefixes.PAGOdAPrefixes.expandIRI(answer));
				if (DLClauseHelper.isTautologyAboutDifferentFrom(clause))
					continue;
				
				tBoxAxiom = m_encoder.getProgram().getEquivalentAxiom(clause);
				addRelevantClauseToRecord(clause);
				m_tBoxAxioms.add(tBoxAxiom);
			}
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		} finally {
			if (answers != null) answers.dispose();
		}

		for (OWLAxiom axiom : m_tBoxAxioms) {
			Logger_MORe.logTrace(axiom);
			addAxiomToRecord(axiom);
		}

		Logger_MORe.logInfo( m_tBoxAxioms.size() + " TBox axioms added to the relevant ontology");
		Logger_MORe.logInfo("Ontology extraction DONE");
		Logger_MORe.logInfo(t.duration());	
	}
	
	public OWLOntology getRelevantOntologyFromRecord(){
		return m_multiRecord.getRelevantOntology();
	}
	
	protected void addRelevantClauseToRecord(DLClause clause){
		m_multiRecord.addRelevantClauses(clause);
	}
	
	protected void addAxiomToRecord(OWLAxiom axiom){
		m_manager.addAxiom(m_multiRecord.getRelevantOntology(), axiom);
	}
	
}
