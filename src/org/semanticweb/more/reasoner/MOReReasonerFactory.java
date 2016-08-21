package org.semanticweb.more.reasoner;

import org.semanticweb.owlapi.model.OWLOntology;

import org.semanticweb.owlapi.reasoner.IllegalConfigurationException;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerConfiguration;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;

/**
 * Factory for the OWLAPI reasoner implementation of the MORe reasoner.
 * 
 * @author aarmas
 * 
 */
public class MOReReasonerFactory implements OWLReasonerFactory {
	
	@Override
	public OWLReasoner createReasoner(OWLOntology ontology) {
		return createMoreReasoner(ontology, true, new MOReReasonerConfiguration(), null, null);
	}

	@Override
	public MOReReasoner createReasoner(OWLOntology ontology,
			OWLReasonerConfiguration config)
			throws IllegalConfigurationException {
		return createMoreReasoner(ontology, true, config, null, null);
	}

	@Override
	public MOReReasoner createNonBufferingReasoner(OWLOntology ontology) {
		return createMoreReasoner(ontology, false, new MOReReasonerConfiguration(), null, null);
	}

	@Override
	public MOReReasoner createNonBufferingReasoner(OWLOntology ontology,
			OWLReasonerConfiguration config)
			throws IllegalConfigurationException {
		return createMoreReasoner(ontology, false, config, null, null);
	}
	
	public MOReReasoner createReasoner(
			OWLOntology ontology, 
			OWLReasonerFactory owl2ReasonerFactory, 
			OWLReasonerConfiguration owl2ReasonerConfiguration) {
		return createMoreReasoner(ontology, true, new MOReReasonerConfiguration(), owl2ReasonerFactory, owl2ReasonerConfiguration);
	}
	
	public MOReReasoner createReasoner(
			OWLOntology ontology, 
			MOReReasonerConfiguration moreConfig, 
			OWLReasonerFactory owl2ReasonerFactory, 
			OWLReasonerConfiguration owl2ReasonerConfiguration) 
					throws IllegalConfigurationException {
		return createMoreReasoner(ontology, true, moreConfig, owl2ReasonerFactory, owl2ReasonerConfiguration);
	}
	
	public MOReReasoner createNonBufferingReasoner(
			OWLOntology ontology, 
			OWLReasonerFactory owl2ReasonerFactory, 
			OWLReasonerConfiguration owl2ReasonerConfiguration) {
		return createMoreReasoner(ontology, false, new MOReReasonerConfiguration(), owl2ReasonerFactory, owl2ReasonerConfiguration);
	}

	public MOReReasoner createNonBufferingReasoner(
			OWLOntology ontology,
			OWLReasonerConfiguration moreConfig, 
			OWLReasonerFactory owl2ReasonerFactory, 
			OWLReasonerConfiguration owl2ReasonerConfiguration)
			throws IllegalConfigurationException {
		return createMoreReasoner(ontology, false, moreConfig, owl2ReasonerFactory, owl2ReasonerConfiguration);
	}
	
	

	protected MOReReasoner createMoreReasoner(
			OWLOntology ontology,
			boolean isBufferingMode, 
			OWLReasonerConfiguration config, 
			OWLReasonerFactory owl2ReasonerFactory, 
			OWLReasonerConfiguration owl2ReasonerConfiguration)
			throws IllegalConfigurationException {

		if (!(config instanceof MOReReasonerConfiguration))
			throw new IllegalConfigurationException("configuration needs to be an instance of MOReReasonerConfiguration", config);
		MOReReasoner more = new MOReReasoner(ontology, isBufferingMode, (MOReReasonerConfiguration) config, new OWL2ReasonerManager(owl2ReasonerFactory, owl2ReasonerConfiguration));
		return more;
	
	}
		
	@Override
	public String getReasonerName() {
		return "MORe_v0.2.0";
	}

}
