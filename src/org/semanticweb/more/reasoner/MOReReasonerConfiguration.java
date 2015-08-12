package org.semanticweb.more.reasoner;

import org.semanticweb.owlapi.reasoner.FreshEntityPolicy;
import org.semanticweb.owlapi.reasoner.IndividualNodeSetPolicy;
import org.semanticweb.owlapi.reasoner.OWLReasonerConfiguration;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;
import org.semanticweb.owlapi.reasoner.ReasonerProgressMonitor;

import uk.ac.ox.cs.pagoda.query.ClassificationQueryType;

public class MOReReasonerConfiguration implements OWLReasonerConfiguration{

	public final boolean integrateRanges;
	public final boolean rewriteInverses;
	public final boolean eliminateForgettableRoles;
	public final boolean useParallelStores;
	public final boolean useMultiStageMaterialisation;
//	public final boolean useImprovedELlowerBoundRules;
	public final boolean useRDFox;
	public final ClassificationQueryType queryType;
	public final boolean saveOntologyForOWL2Reasoner;
	public final String suffixForSavedOntology;
	
	public MOReReasonerConfiguration(){
		this.integrateRanges = true;
		this.rewriteInverses = true;
		this.eliminateForgettableRoles = true;
		this.useParallelStores = true;
		this.useMultiStageMaterialisation = true;
		this.queryType = ClassificationQueryType.INDIVIDUAL;
		this.useRDFox = false;
		this.saveOntologyForOWL2Reasoner = false;
		this.suffixForSavedOntology = null;
	}
	
	public MOReReasonerConfiguration(boolean useRDFox){
		this.useRDFox = useRDFox;		
		this.integrateRanges = true;
		this.rewriteInverses = true;
		this.eliminateForgettableRoles = true;
		this.useParallelStores = true;
		this.useMultiStageMaterialisation = true;
		this.queryType = ClassificationQueryType.INDIVIDUAL;
		this.saveOntologyForOWL2Reasoner = false;
		this.suffixForSavedOntology = null;
	}
	
	public MOReReasonerConfiguration(boolean integrateRanges, boolean rewriteInverses,
			boolean eliminateForgettableRoles, boolean useParallelStores,
			boolean useMultiStageMaterialisation, //boolean useImprovedELlowerBoundRules,
			boolean useRDFox){
		this.integrateRanges = integrateRanges;
		this.rewriteInverses = rewriteInverses;
		this.eliminateForgettableRoles = eliminateForgettableRoles;
		this.useParallelStores = useParallelStores;
		this.useMultiStageMaterialisation = useMultiStageMaterialisation;
//		this.useImprovedELlowerBoundRules = useImprovedELlowerBoundRules;
		this.useRDFox = useRDFox;
		this.queryType = ClassificationQueryType.INDIVIDUAL;
		this.saveOntologyForOWL2Reasoner = false;
		this.suffixForSavedOntology = null;
	}
	
	public MOReReasonerConfiguration(boolean integrateRanges, boolean rewriteInverses,
			boolean eliminateForgettableRoles, boolean useParallelStores,
			boolean useMultiStageMaterialisation, //boolean useImprovedELlowerBoundRules,
			boolean useRDFox, ClassificationQueryType queryType,
			boolean saveOntologyForOWL2Reasoner,
			String suffix){
		this.integrateRanges = integrateRanges;
		this.rewriteInverses = rewriteInverses;
		this.eliminateForgettableRoles = eliminateForgettableRoles;
		this.useParallelStores = useParallelStores;
		this.useMultiStageMaterialisation = useMultiStageMaterialisation;
//		this.useImprovedELlowerBoundRules = useImprovedELlowerBoundRules;
		this.useRDFox = useRDFox;
		this.queryType = queryType;
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
