package uk.ac.ox.cs.pagoda.multistage;

import java.io.File;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.semanticweb.more.pagoda.IndividualManager;
import org.semanticweb.more.pagoda.rules.DatalogProgram4Classification;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.more.util.Utility;
import org.semanticweb.owlapi.model.OWLClass;

import uk.ac.ox.cs.JRDFox.JRDFStoreException;
import uk.ac.ox.cs.JRDFox.Prefixes;
import uk.ac.ox.cs.JRDFox.store.DataStore.UpdateType;
import uk.ac.ox.cs.JRDFox.store.TupleIterator;
import uk.ac.ox.cs.pagoda.multistage.treatment.Pick4NegativeConceptNaive;
import uk.ac.ox.cs.pagoda.multistage.treatment.Treatment;
import uk.ac.ox.cs.pagoda.multistage.treatment.Treatment4Classification;
import uk.ac.ox.cs.pagoda.query.AnswerTuple;
import uk.ac.ox.cs.pagoda.query.GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly;
import uk.ac.ox.cs.pagoda.reasoner.light.BasicQueryEngine;
import uk.ac.ox.cs.pagoda.reasoner.light.RDFoxTripleManager;
import uk.ac.ox.cs.pagoda.rules.Program;
import uk.ac.ox.cs.pagoda.util.MyPrefixes;
import uk.ac.ox.cs.pagoda.util.Timer;
import uk.ac.ox.cs.pagoda.util.Utility_PAGOdA;


public class MultiStageQueryEngine extends StageQueryEngine {//TODO recover distinction between MultiStageQueryEngine and idem4Classification so I have the old methods as reference

	RDFoxTripleManager tripleManager;
	IndividualManager indManager;

	public MultiStageQueryEngine(String name, boolean checkValidity, IndividualManager indManager) {
		super(name, checkValidity);
		tripleManager = new RDFoxTripleManager(store, false);
		this.indManager = indManager;
	}

//	public void materialiseMultiStage(DatalogProgram4Classification dProgram, GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly gap) {//inspired by materialiseRestrictedly in this class originally
//		materialise("lower program", dProgram.getRLprogram().toString());
//		Program generalProgram = dProgram.getGeneral();
//		MultiStageUpperProgram4Classification program = new MultiStageUpperProgram4Classification(generalProgram, dProgram.getUpperBottomStrategy());
//		Treatment4Classification treatment = new Treatment4Classification(this, program);
//		materialiseMultiStage(program, treatment, gap);
//		treatment.dispose();
//	}
	public void materialiseMultiStage(
			DatalogProgram4Classification dProgram, 
			String skolemAboxFileName,
			GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly gap, 
			BasicQueryEngine lowerStore) {//inspired by materialiseRestrictedly in this class originally
		addExtraTriplesFromLowerStore(lowerStore, indManager);
		
		Utility.printAllTriples(getDataStore());
		
		importRDFData("Skolem data", skolemAboxFileName);
		Program generalProgram = dProgram.getGeneral();
		MultiStageUpperProgram4Classification program = new MultiStageUpperProgram4Classification(generalProgram, dProgram.getUpperBottomStrategy());
		Treatment4Classification treatment = new Treatment4Classification(this, program);
		materialiseMultiStage(program, treatment, gap);
		treatment.dispose();
	}

	private void materialiseMultiStage(
			MultiStageUpperProgram program, 
			Treatment4Classification treatment, 
			GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly gap) {
		String programName = "multi-stage upper program"; 
		Logger_MORe.logInfo(name + " store is materialising " + programName +  " ..."); 
		Timer t = new Timer();

		long tripleCountBeforeMat = 0; 

		program.saveDatalogRules(Utility_PAGOdA.TempDirectory + "/multi_datalog.dlog");

		Collection<Violation> violations = null;
		int iteration = 0;
		Timer subTimer = new Timer(); 
		boolean incrementally = false; 
		try {
			while (true) {
				long oldTripleCount = store.getTriplesCount();

				subTimer.reset();
				Logger_MORe.logInfo("Iteration " + ++iteration + ": ");

				incrementally = (iteration != 1);

				if (incrementally)
					gap.compileFromFile(null);
				else{
					tripleCountBeforeMat = oldTripleCount;
					gap.compileFromFile(new File(Utility_PAGOdA.TempDirectory + "/multi_datalog.dlog"));
				}
//				Utility.printStoreToFile(store, "multistageMaterialisationIter"+iteration);
//				Utility.printPredicatesSummaryOfStoreToFile(store, "multistageMaterialisationIter"+iteration);
				Utility.printAllTriples(getDataStore());
				gap.registerGapTuples(); //PAGOdA does not add the gap when doing multistage because the multistage store cannot be used for tracking, but we want to register
				//which instantiation individuals have a gap and which don't to detect classes that may be fully classified at this point.
				//this is an alternative to addGapBackTo that registers information about which instantiation individuals have a gap but
				//doesn't add gap tuples to the store. 

				long tripleCount = store.getTriplesCount(); 
				Logger_MORe.logDebug(name + " store after materialising datalog-rules: " + tripleCount + " (" + (tripleCount - oldTripleCount) + " new)");
				Logger_MORe.logDebug("Time to materialise datalog-rules: " + subTimer.duration()); 

				subTimer.reset(); 
				if ((violations = program.isIntegrated(this, incrementally)) == null || violations.size() == 0) {
					store.clearRulesAndMakeFactsExplicit();
					Logger_MORe.logDebug(name + " store after materialising " + programName + ": " + tripleCount + " (" + (tripleCount - tripleCountBeforeMat) + " new)");
					Logger_MORe.logInfo(name + " store is DONE for multi-stage materialising in " + t.duration() + " seconds.");
					return;
				}
				Logger_MORe.logDebug("Time to detect violations: " + subTimer.duration()); 

				store.makeFactsExplicit();
				
				subTimer.reset(); 
				oldTripleCount = store.getTriplesCount(); 
				for (Violation v : violations) {
					Timer localTimer = new Timer(); 
					int number = v.size(); 
					long vOldCounter = store.getTriplesCount();
					
					treatment.makeSatisfied(v, gap);
					
					Logger_MORe.logDebug("Time to make the constraint being satisfied: " + localTimer.duration() + " " + number + " tuples for " + v.getConstraint()); 
					Logger_MORe.logDebug("tuple number: " + v.size() + " before: " + vOldCounter + " after: " + store.getTriplesCount() + " (" + (store.getTriplesCount() - vOldCounter) + " new) ." ); 
				}
				Logger_MORe.logDebug(name + " store after adding facts for violations: " + (tripleCount = store.getTriplesCount()) + " (" + (tripleCount - oldTripleCount) + " new)");
				Logger_MORe.logDebug("Time to add triples for violations: " + subTimer.duration()); 
			}
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		} 
	}
	
	
	
	
	public Set<?>[] materialiseRestrictedlyAndGetGap(DatalogProgram4Classification dProgram) {
		Program generalProgram = dProgram.getGeneral();
		MultiStageUpperProgram4Classification program = new MultiStageUpperProgram4Classification(generalProgram, dProgram.getUpperBottomStrategy());
		Treatment treatment = new Treatment4Classification(this, program);
		Set<?>[] ret = materialise(program, treatment, true);
		treatment.dispose();
		return ret; 
	}
	
	public void materialiseRestrictedly(DatalogProgram4Classification dProgram) {
		Program generalProgram = dProgram.getGeneral();
		MultiStageUpperProgram4Classification program = new MultiStageUpperProgram4Classification(generalProgram, dProgram.getUpperBottomStrategy());
		Treatment treatment = new Pick4NegativeConceptNaive(this, program);
		materialise(program, treatment, false);
		treatment.dispose();
	}

	protected Set<?>[] materialise(MultiStageUpperProgram4Classification program, Treatment treatment, boolean registerPredicatesWithGap) {
		//based on materialise(MultiStageUpperProgram, Treatment, GapByStore4ID)

		Set<?>[] ret = new Set<?>[3];
		if (registerPredicatesWithGap){
			ret[0] = new HashSet<OWLClass>();//classes with candidate subsumers
			ret[1] = new HashSet<String>();//potentiallyUnsatClasses
			ret[2] = new HashSet<String>();//candidate subsumers // do I even need to store these?
		}

		String programName = "multi-stage upper program"; 
		Logger_MORe.logInfo(name + " store is materialising " + programName +  " ..."); 
		Timer t = new Timer();

		long tripleCountBeforeMat = 0; 

		Collection<Violation> violations = null;
		int iteration = 0;
		Timer subTimer = new Timer(); 
		boolean incrementally = false; 
		TupleIterator iter = null;
		try {
			while (true) {
				long oldTripleCount = store.getTriplesCount();

				subTimer.reset();
				Logger_MORe.logInfo("Iteration " + ++iteration + ": ");

				incrementally = (iteration != 1);

				if (incrementally)
					store.setNumberOfThreads(1);
				else{
					tripleCountBeforeMat = oldTripleCount;
					store.importFiles(new File[]{new File(program.getOutputPath())}, new Prefixes(), UpdateType.Add, true);
				}
				store.applyReasoning(incrementally);
				store.setNumberOfThreads(matNoOfThreads);

				if (registerPredicatesWithGap){ 
					//here we are basically imitating GapByStore4ID, can't we just add the relevant methods to that class and use it class here?

					try{
						iter = internal_evaluateAgainstIDBs("select ?x ?z where { ?x " + MyPrefixes.PAGOdAPrefixes.expandText("rdf:type") + " ?z . }");
						for (long multi = iter.open(); multi != 0 ; multi = iter.getNext()){
							OWLClass c = indManager.getClass4Individual(RDFoxTripleManager.getRawTerm(iter.getResource(0))); 
							if (c != null){
								String s = RDFoxTripleManager.getRawTerm(iter.getResource(1));
								if (s.equals(MyPrefixes.PAGOdAPrefixes.expandText("owl:Nothing"))){
									((Set<String>) ret[1]).add(RDFoxTripleManager.getRawTerm(iter.getResource(0)));
									((Set<OWLClass>) ret[0]).add(c);
								}
								else{
									((Set<OWLClass>) ret[0]).add(c);
									((Set<String>) ret[2]).add(RDFoxTripleManager.getRawTerm(iter.getResource(1)));	
								}
							}
						}
					}
					catch (JRDFStoreException e){
						e.printStackTrace();
						if (iter != null) iter.dispose();
					}
					finally{
						if (iter != null) iter.dispose();
					}

				}


				long tripleCount = store.getTriplesCount(); 
				Logger_MORe.logDebug(name + " store after materialising datalog-rules: " + tripleCount + " (" + (tripleCount - oldTripleCount) + " new)");
				Logger_MORe.logDebug("Time to materialise datalog-rules: " + subTimer.duration()); 

				subTimer.reset(); 
				//TODO revise this chunk to make sure inconsistencies do not make us stop materialising FIXME
				if ((violations = program.isIntegrated(this, incrementally)) == null || violations.size() == 0) {
					store.clearRulesAndMakeFactsExplicit();
					Logger_MORe.logDebug(name + " store after materialising " + programName + ": " + tripleCount + " (" + (tripleCount - tripleCountBeforeMat) + " new)");
					Logger_MORe.logInfo(name + " store is DONE for multi-stage materialising in " + t.duration() + " seconds.");
					return ret;//isValid() ? 1 : 0;
				}
				Logger_MORe.logDebug("Time to detect violations: " + subTimer.duration()); 

				store.makeFactsExplicit();
				
//				first.printAllTriples(getDataStore());
				
				subTimer.reset(); 
				oldTripleCount = store.getTriplesCount(); 
				for (Violation v : violations) {
					Timer localTimer = new Timer(); 
					int number = v.size(); 
					long vOldCounter = store.getTriplesCount();
					
					if (registerPredicatesWithGap){
						for (AnswerTuple tuple : ((Treatment4Classification) treatment).makeSatisfiedAndReturnAddedTuples(v)){
							OWLClass c = indManager.getClass4Individual(tuple.getRawTerm(0)); 
							if (c != null){
								String s = tuple.getRawTerm(1);
								if (s.equals(MyPrefixes.PAGOdAPrefixes.expandText("owl:Nothing"))){
									((Set<String>) ret[1]).add(tuple.getRawTerm(0));
									((Set<OWLClass>) ret[0]).add(c);
								}
								else{
									((Set<OWLClass>) ret[0]).add(c);
									((Set<String>) ret[2]).add(tuple.getRawTerm(1));	
								}
							}
						}
					}
					else{
						if (!treatment.makeSatisfied(v)) {
							//						validMaterialisation = false;
							//						Utility.logInfo(name + " store FAILED for multi-stage materialisation in " + t.duration() + " seconds."); 
							Logger_MORe.logInfo(name + " store could not make violation satisfied for multi-stage materialisation, but we'll keep going!.");
							//						return 0; 
						}	
					}
					
					Logger_MORe.logDebug("Time to make the constraint being satisfied: " + localTimer.duration() + " " + number + " tuples for " + v.getConstraint()); 
					Logger_MORe.logDebug("tuple number: " + v.size() + " before: " + vOldCounter + " after: " + store.getTriplesCount() + " (" + (store.getTriplesCount() - vOldCounter) + " new) ." ); 
				}
				Logger_MORe.logDebug(name + " store after adding facts for violations: " + (tripleCount = store.getTriplesCount()) + " (" + (tripleCount - oldTripleCount) + " new)");
				Logger_MORe.logDebug("Time to add triples for violations: " + subTimer.duration()); 
			}
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		} 
		return ret; 
	}

	
			
}

