package org.semanticweb.more.lsignature;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.semanticweb.more.reasoner.ListProcessor;
import org.semanticweb.more.reasoner.LocalityInfo;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.more.visitors.OWLFragmentVisitor;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLOntology;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;

public class LsignatureExtractor_reducedGreedyness extends LsignatureExtractor{

	protected Set<OWLAxiom> nonFragmentAxiomsStillNonLocal = new HashSet<OWLAxiom>();


	public LsignatureExtractor_reducedGreedyness(){
		super();
	}

	public Set<OWLEntity> findLsignature(OWLOntology o, LogicFragment f){
		ontology = o;
		fragment = f;
		findGlobalEntities();


		long tExt = System.currentTimeMillis();
		initialiseLsignature();
		int currentSize = lSignature.size();
		int previousSize = 0;
		while (currentSize != previousSize) {
			reduceLsignature();
			previousSize = currentSize;
			currentSize = lSignature.size();
		}
		tExt = System.currentTimeMillis() - tExt;
		Logger_MORe.logDebug("Lsignature extraction took " + tExt + " milliseconds");// and "+ nIterations + " iterations");
		Logger_MORe.logDebug("Lsignature of size " + lSignature.size());
		int nonInternalEntitiesInSignature = 0;
		for (OWLEntity e : lSignature)
			if (!e.toString().contains("internal:"))
				nonInternalEntitiesInSignature++;
		Logger_MORe.logDebug("with " + nonInternalEntitiesInSignature + " nonInternal entities");

		return lSignature;
	}


	@Override
	protected void initialiseLsignature() {

		LinkedList<List<Set<OWLEntity>>> nondeterministicSolutions = new LinkedList<List<Set<OWLEntity>>>();

		OWLFragmentVisitor fragmentVisitor = getFragmentVisitor();

		lSignature = ontology.getSignature();
		lSignature.add(new OWLDataFactoryImpl().getOWLThing());//in case it's not explicitly in the ontology
		lSignature.add(new OWLDataFactoryImpl().getOWLNothing());//in case it's not explicitly in the ontology
		compSignature = new HashSet<OWLEntity>();
		lSignatureModule =  new HashSet<OWLAxiom>();
		classesInvisibleInL = ontology.getClassesInSignature();

		for (OWLAxiom axiom : ontology.getAxioms()) {
			axiom.accept(fragmentVisitor);	
			if (fragmentVisitor.isInFragment()){
				nAxiomsInFragment++;
				lSignatureModule.add(axiom);			
				classesInvisibleInL.removeAll(axiom.getClassesInSignature());
			}
			else{

					Logger_MORe.logTrace(axiom.toString() + " not in fragment " + fragment.toString());

				LocalityInfo locInfo = localityChecker.isLocalAxiom(axiom, lSignature, globalEntities);
				if (!locInfo.is()) {
					if (locInfo.canMake()) {
						if (locInfo.getSolutions().size() == 1)
							//actually some kind of greedyness may have been applied laready in constructing this, so this is not guaramteed to be totally deterministic
							//but we could anotate solutions with this info to check if this is the case...
							for (Set<OWLEntity> s : locInfo.getSolutions()){
								compSignature.addAll(s);
								lSignature.removeAll(s);
							}
						else{
							nonFragmentAxiomsStillNonLocal.add(axiom);
							if (compSignature.isEmpty())
								nondeterministicSolutions.add(locInfo.getSolutions());
						}
					}
					else{
						Logger_MORe.logInfo("empty lSignature due to axiom " + axiom.toString());
						lSignature = new HashSet<OWLEntity>(); //and in this case compSignature stays with its current value of ontology.getSignature()
						compSignature = ontology.getSignature();
						lSignatureModule = new HashSet<OWLAxiom>();
						return;
					}
				}
			}
		}


		Logger_MORe.logInfo(lSignatureModule.size() + " axioms in fragment " + fragment.toString());

		if (compSignature.isEmpty()){

			//				System.out.println("no deterministic solutions in the initialisation phase");

			//It is extremely unlikely (is it?) that none of the axioms outside the fragment can be localised in a deterministic way, 
			//but if that is the case then maybe we should pick only a few of them that are not "too nondeterministic" to get started and 
			//guide the choices about the more nondeterministic ones
			compSignature = new ListProcessor().getMinimalCombination(nondeterministicSolutions, lSignature.size());
			lSignature.removeAll(compSignature);
			lSignatureModule.removeAll(nonFragmentAxiomsStillNonLocal);
		}
		else{
			//				System.out.println("deterministic solutions in the initialisation phase");
		}

		//			System.out.println("compSignature of size " + compSignature.size());

		//			//and now remove also all the symbols in the bot module for the current complementary signature
		//			for (OWLAxiom a : moduleExtractor.extract(compSignature)){
		//				compSignature.addAll(a.getClassesInSignature());	
		//			}
		//			
		//			System.out.println("compSignature of size " + compSignature.size() + " after adding to it the entities in the compModule");

		
	}



	protected void reduceLsignature(){

		LinkedList<List<Set<OWLEntity>>> nondeterministicSolutions = new LinkedList<List<Set<OWLEntity>>>();
		boolean someDeterministicSolsFound = false;

		Set<OWLAxiom> newLocalNonFragmentAxiomsDet = new HashSet<OWLAxiom>();
		Set<OWLAxiom> newLocalNonFragmentAxiomsNondet = new HashSet<OWLAxiom>();
		for (OWLAxiom axiom : nonFragmentAxiomsStillNonLocal){

			LocalityInfo locInfo = localityChecker.isLocalAxiom(axiom, lSignature, globalEntities);
			if (!locInfo.is()) 
				if (locInfo.canMake()) {
					if (locInfo.getSolutions().size() == 1){
						for (Set<OWLEntity> s: locInfo.getSolutions()){
							compSignature.addAll(s);
							lSignature.removeAll(s);
						}
						newLocalNonFragmentAxiomsDet.add(axiom);
						someDeterministicSolsFound = true;
					}
					else{
						if (!someDeterministicSolsFound)
							nondeterministicSolutions.add(locInfo.getSolutions());
						newLocalNonFragmentAxiomsNondet.add(axiom);
					}
				} 
				else{
					Logger_MORe.logInfo("empty lSignature due to axiom " + axiom.toString());
					lSignature = new HashSet<OWLEntity>(); 
					compSignature = ontology.getSignature();
					lSignatureModule = new HashSet<OWLAxiom>();
					return;
				}
		}
		nonFragmentAxiomsStillNonLocal.removeAll(newLocalNonFragmentAxiomsDet);

		Set<OWLAxiom> newLocalFragmentAxiomsDet = new HashSet<OWLAxiom>();
		Set<OWLAxiom> newLocalFragmentAxiomsNondet = new HashSet<OWLAxiom>();
		for (OWLAxiom axiom : lSignatureModule) {
			//LocalityInfo locInfo = localityChecker.isLocalAxiom(axiom, lSignature);
			if (!lSignature.containsAll(axiom.getSignature())){
				LocalityInfo locInfo = localityChecker.isLocalAxiom(axiom, lSignature, globalEntities);
				if (!locInfo.is()) 
					if (locInfo.canMake()) {

						if (locInfo.getSolutions().size() == 1) {
							for (Set<OWLEntity> s: locInfo.getSolutions()){
								compSignature.addAll(s);
								lSignature.removeAll(s);
							}
							newLocalFragmentAxiomsDet.add(axiom);
							someDeterministicSolsFound = true;
						}
						else{
							if (!someDeterministicSolsFound)
								nondeterministicSolutions.add(locInfo.getSolutions());
							newLocalFragmentAxiomsNondet.add(axiom);	
						}
					} 
					else{
						Logger_MORe.logInfo("empty lSignature due to axiom " + axiom.toString());
						lSignature = new HashSet<OWLEntity>(); 
						compSignature = ontology.getSignature();
						lSignatureModule = new HashSet<OWLAxiom>();
						return;
					}
			}
		}
		lSignatureModule.removeAll(newLocalFragmentAxiomsDet);

		if (!someDeterministicSolsFound){

			//				System.out.println("no deterministic solutions in this reduction phase");

			Set<OWLEntity> notInLsignature = new ListProcessor().getMinimalCombination(nondeterministicSolutions, lSignature.size());
			compSignature.addAll(notInLsignature);
			lSignatureModule.removeAll(newLocalFragmentAxiomsNondet);
//			lSignatureModule.removeAll(newLocalNonFragmentAxiomsNondet);//unnecessary because we never put any nonFragment axioms in this set to begin with
		}
		else{
			//				System.out.println("deterministic solutions in this reduction phase");
		}

		lSignature.removeAll(compSignature);		
	}

	public void resetValues(){ //better way of doing this?
		super.resetValues();
		nonFragmentAxiomsStillNonLocal = null;
	}

}
