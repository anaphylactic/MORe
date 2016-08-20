package org.semanticweb.more.reasoner;

import org.semanticweb.owlapi.reasoner.FreshEntityPolicy;
import org.semanticweb.owlapi.reasoner.IndividualNodeSetPolicy;
import org.semanticweb.owlapi.reasoner.OWLReasonerConfiguration;
import org.semanticweb.owlapi.reasoner.ReasonerProgressMonitor;

public class MOReReasonerConfiguration implements OWLReasonerConfiguration{

	public final boolean integrateRanges;
	public final boolean rewriteInverses;
	public final boolean eliminateForgettableRoles;
	public final boolean useMultiStageMaterialisation;
	public final boolean useRDFox;
	public final boolean saveOntologyForOWL2Reasoner;
	public final String suffixForSavedOntology;
	
	public MOReReasonerConfiguration(){
		this.integrateRanges = true;
		this.rewriteInverses = true;
		this.eliminateForgettableRoles = true;
		this.useMultiStageMaterialisation = true;
		this.useRDFox = false;
		this.saveOntologyForOWL2Reasoner = false;
		this.suffixForSavedOntology = null;
	}
	
	public MOReReasonerConfiguration(boolean useRDFox){
		this.useRDFox = useRDFox;		
		this.integrateRanges = true;
		this.rewriteInverses = true;
		this.eliminateForgettableRoles = true;
		this.useMultiStageMaterialisation = true;
		this.saveOntologyForOWL2Reasoner = false;
		this.suffixForSavedOntology = null;
	}
	
	public MOReReasonerConfiguration(boolean integrateRanges, boolean rewriteInverses,
			boolean eliminateForgettableRoles,
			boolean useMultiStageMaterialisation, 
			boolean useRDFox){
		this.integrateRanges = integrateRanges;
		this.rewriteInverses = rewriteInverses;
		this.eliminateForgettableRoles = eliminateForgettableRoles;
		this.useMultiStageMaterialisation = useMultiStageMaterialisation;
		this.useRDFox = useRDFox;
		this.saveOntologyForOWL2Reasoner = false;
		this.suffixForSavedOntology = null;
	}
	
	public MOReReasonerConfiguration(boolean integrateRanges, boolean rewriteInverses,
			boolean eliminateForgettableRoles,
			boolean useMultiStageMaterialisation, 
			boolean useRDFox, boolean saveOntologyForOWL2Reasoner,
			String suffix){//this constructor is meant for performance testing purposes
		this.integrateRanges = integrateRanges;
		this.rewriteInverses = rewriteInverses;
		this.eliminateForgettableRoles = eliminateForgettableRoles;
		this.useMultiStageMaterialisation = useMultiStageMaterialisation;
		this.useRDFox = useRDFox;
		this.saveOntologyForOWL2Reasoner = saveOntologyForOWL2Reasoner;
		this.suffixForSavedOntology = suffix;
	}
	
	@Override
	public FreshEntityPolicy getFreshEntityPolicy() {
		return null;
	}

	@Override
	public IndividualNodeSetPolicy getIndividualNodeSetPolicy() {
		return null;
	}

	@Override
	public ReasonerProgressMonitor getProgressMonitor() {
		return null;
	}

	@Override
	public long getTimeOut() {
		return 0;
	}

}
