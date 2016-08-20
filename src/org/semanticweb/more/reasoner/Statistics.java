package org.semanticweb.more.reasoner;

import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.owlapi.model.OWLOntology;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;

public class Statistics {

	
	protected long nClassesInSignature;
	protected int totalAxioms;
	
	protected long lSignatureSize;
	protected long extraLsigWithRangeAndInvRewOptimisations;
	protected double tLsignature;
	
	protected long subsumptionPairsDecidedByELK = 0;
	protected double tELK;
	protected int nELKaxioms;
	
	protected long subsumptionPairsDecidedPAGOdAstyle;
	protected double tPAGOdA;
	protected int nAxiomsGivenToPAGOdA;
	
	
	protected long subsumptionPairsDecidedByHermiT = 0;
	protected double tHermiT;
	protected int nAxiomsGivenToHermiT;
	

	public Statistics(OWLOntology o, boolean usingFancyLsignatureOptimisations, boolean usingPAGOdA){
		nClassesInSignature = o.getClassesInSignature().size();
		if (!o.getClassesInSignature().contains(new OWLDataFactoryImpl().getOWLThing()))
			nClassesInSignature++;
		if (!o.getClassesInSignature().contains(new OWLDataFactoryImpl().getOWLNothing()))
			nClassesInSignature++;
		totalAxioms = o.getAxiomCount();
		if (usingFancyLsignatureOptimisations)
			extraLsigWithRangeAndInvRewOptimisations = 0;
		else extraLsigWithRangeAndInvRewOptimisations = -1;
		if (usingPAGOdA)
			subsumptionPairsDecidedPAGOdAstyle = 0;
		else subsumptionPairsDecidedPAGOdAstyle = -1;
	}


	public void updateLsignatureSize(int n, boolean registerIncrementDueToFancyOptimisations){
		if (registerIncrementDueToFancyOptimisations)
			extraLsigWithRangeAndInvRewOptimisations = n - lSignatureSize;
		lSignatureSize = n;
		subsumptionPairsDecidedByELK = n*nClassesInSignature;
		long total = getNpotentialSubsumptionPairs();
		subsumptionPairsDecidedByHermiT = total - subsumptionPairsDecidedByELK;
	}
	public void updateLsignatureTime(double t){
		tLsignature = t;
	}
	public long getLsignatureSize(){
		return lSignatureSize;
	}
	
	
	public void updateNelkAxioms(int n){
		nELKaxioms = n;
	}
	public void updateELKtime(double t){
		tELK = t;
	}
	

	public void updatePairsDecidedPAGOdAstyle(int n){
		subsumptionPairsDecidedPAGOdAstyle = n;
		subsumptionPairsDecidedByHermiT = getNpotentialSubsumptionPairs() - subsumptionPairsDecidedByELK - n;
		
	}
	public void updateNaxiomsForPAGOdA(int n){
		nAxiomsGivenToPAGOdA = n;
	}
	public void updatePAGOdAtime(double t){
		tPAGOdA = t;
	}
	
	
	public void updatePairsDecidedByHermiT(int n){
		subsumptionPairsDecidedByHermiT = n;
		subsumptionPairsDecidedPAGOdAstyle = getNpotentialSubsumptionPairs() - subsumptionPairsDecidedByELK - n;
		
	}
	public void updateNaxiomsForHermiT(int n){
		nAxiomsGivenToHermiT = n;
	}
	public void updateHermiTtime(double t){
		tHermiT = t;
	}
	
	
	public long getNpotentialSubsumptionPairs(){
		return nClassesInSignature*nClassesInSignature;
	}
	
	
	public void printStats(){
		Logger_MORe.logInfo(
				"\npotential subsumption pairs: " + getNpotentialSubsumptionPairs() + 
				"\n\npairs decided by ELK: " + subsumptionPairsDecidedByELK + 
				"\nELK took: " + tELK + "ms" +  
				"\naxioms within ELK's fragment: " + nELKaxioms + 
				"\n\nlSignature of size: " + lSignatureSize + " (" + extraLsigWithRangeAndInvRewOptimisations + " classes extra thanks to fancy optimisations" +
				"\nlSignature extraction took: " + tLsignature +
				"\n\npairs decided by PAGOdA/RDFox: " + subsumptionPairsDecidedPAGOdAstyle + 
				"\nPAGOdA-style reasoning took: " + tPAGOdA + "ms" +
				"\nPAGOdA-style had to deal with: " + nAxiomsGivenToPAGOdA + " axioms" +
				"\n\npairs decided by HermiT (or other): " + subsumptionPairsDecidedByHermiT + 
				"\nHermiT took: " + tHermiT + "ms" +
				"\nHermiT had to deal with: " + nAxiomsGivenToHermiT + " axioms");
	}
}
