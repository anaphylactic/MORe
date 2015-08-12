package org.semanticweb.more.hermit;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.Prefixes;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.HermiT.hierarchy.ClassificationProgressMonitor;
import org.semanticweb.HermiT.hierarchy.DeterministicClassification;
import org.semanticweb.HermiT.hierarchy.Hierarchy;
import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.tableau.Tableau;
import org.semanticweb.owlapi.model.OWLOntology;

public class TailoredHermit extends Reasoner {


	public TailoredHermit(OWLOntology rootOntology) {
		super(rootOntology);
	}


	public TailoredHermit(Configuration configuration, OWLOntology rootOntology) {
		super(configuration, rootOntology);
	}


	//in the upperbound map, classes that are potentially unsatisfiable should be mapped to a set that contains ONLY bot
	public void classifyClasses(Map<AtomicConcept, Collection<AtomicConcept>> upperBoundCandidateSubsumers, Map<AtomicConcept, Collection<AtomicConcept>> lowerBoundKnownSubsumers) {
		checkPreConditions();
		if (m_atomicConceptHierarchy==null) {
			Set<AtomicConcept> relevantAtomicConcepts=new HashSet<AtomicConcept>();
			relevantAtomicConcepts.add(AtomicConcept.THING);
			relevantAtomicConcepts.add(AtomicConcept.NOTHING);
			
			//not only the concepts we want to classify are relevant, all non internal concepts are 
			//since we want to know if any of them is a superconcept of one of the concepts we want to classify
			for (AtomicConcept atomicConcept : m_dlOntology.getAllAtomicConcepts())
				if (!Prefixes.isInternalIRI(atomicConcept.getIRI()))
					relevantAtomicConcepts.add(atomicConcept);
			
			if (!m_isConsistent)
				m_atomicConceptHierarchy=Hierarchy.emptyHierarchy(relevantAtomicConcepts,AtomicConcept.THING,AtomicConcept.NOTHING);
			else {
				try {
//					final int numRelevantConcepts=relevantAtomicConcepts.size();
					final int numConceptsToBeClassified = upperBoundCandidateSubsumers.keySet().size();
					if (m_configuration.reasonerProgressMonitor!=null)
						m_configuration.reasonerProgressMonitor.reasonerTaskStarted("Building the class hierarchy...");
					ClassificationProgressMonitor progressMonitor=new ClassificationProgressMonitor() {
						protected int m_processedConcepts=0;
						public void elementClassified(AtomicConcept element) {
							m_processedConcepts++;
							if (m_configuration.reasonerProgressMonitor!=null)
//								m_configuration.reasonerProgressMonitor.reasonerTaskProgressChanged(m_processedConcepts,numRelevantConcepts);
								m_configuration.reasonerProgressMonitor.reasonerTaskProgressChanged(m_processedConcepts,numConceptsToBeClassified);
						}
					};
					m_atomicConceptHierarchy=classifyAtomicConcepts(
							getTableau(),
							progressMonitor,
							AtomicConcept.THING,
							AtomicConcept.NOTHING,
							relevantAtomicConcepts, 
							m_configuration.forceQuasiOrderClassification, 
							upperBoundCandidateSubsumers, 
							lowerBoundKnownSubsumers);
					if (m_instanceManager!=null)
						m_instanceManager.setToClassifiedConceptHierarchy(m_atomicConceptHierarchy);
				}
				finally {
					if (m_configuration.reasonerProgressMonitor!=null)
						m_configuration.reasonerProgressMonitor.reasonerTaskStopped();
				}
			}
		}
	}

	protected Hierarchy<AtomicConcept> classifyAtomicConcepts(
			Tableau tableau,
			ClassificationProgressMonitor progressMonitor,
			AtomicConcept topElement,
			AtomicConcept bottomElement,
			Set<AtomicConcept> elements,
			boolean forceQuasiOrder,
			Map<AtomicConcept, Collection<AtomicConcept>> candidateSubsumers, 
			Map<AtomicConcept, Collection<AtomicConcept>> lowerBoundKnownSubsumers) {
		if (tableau.isDeterministic() && !forceQuasiOrder)
			return new DeterministicClassification(tableau,progressMonitor,topElement,bottomElement,elements).classify();
		else
			return new TailoredQuasiOrderClassification(tableau,progressMonitor,topElement,bottomElement,elements,candidateSubsumers, lowerBoundKnownSubsumers).classify();
	}
}

















