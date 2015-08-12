package org.semanticweb.more.hermit;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;

import org.semanticweb.HermiT.hierarchy.ClassificationProgressMonitor;
import org.semanticweb.HermiT.hierarchy.Hierarchy;
import org.semanticweb.HermiT.hierarchy.HierarchyNode;
import org.semanticweb.HermiT.hierarchy.HierarchySearch.Relation;
import org.semanticweb.HermiT.hierarchy.QuasiOrderClassification;
import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.tableau.ExtensionTable;
import org.semanticweb.HermiT.tableau.Node;
import org.semanticweb.HermiT.tableau.Tableau;

public class TailoredQuasiOrderClassification extends QuasiOrderClassification{

	protected final Map<AtomicConcept, Collection<AtomicConcept>> m_upperBoundSubsumptions;
	protected final Map<AtomicConcept, Collection<AtomicConcept>> m_lowerBoundSubsumptions;


	// protected final Tableau m_tableau;
	// protected final ClassificationProgressMonitor m_progressMonitor;
	// protected final AtomicConcept m_topElement;
	// protected final AtomicConcept m_bottomElement;
	// protected final Set<AtomicConcept> m_elements;
	// protected final Graph<AtomicConcept> m_knownSubsumptions;
	// protected final Graph<AtomicConcept> m_possibleSubsumptions;

	public TailoredQuasiOrderClassification(Tableau tableau,ClassificationProgressMonitor progressMonitor,AtomicConcept topElement,AtomicConcept bottomElement,Set<AtomicConcept> elements,
			Map<AtomicConcept, Collection<AtomicConcept>> upperBoundSubsumptions,Map<AtomicConcept, Collection<AtomicConcept>> lowerBoundSubsumptions) {
		super(tableau,progressMonitor,topElement,bottomElement,elements);
		m_upperBoundSubsumptions = upperBoundSubsumptions;
		m_lowerBoundSubsumptions = lowerBoundSubsumptions;//we probably need here the classification of every concept in the ontology that is already fully classified as well.
		
		//for concepts found to be potentially unsatisfiable, m_upperBoundSubsumptions should map them to the emptyset 
	}

	@Override
	protected Hierarchy<AtomicConcept> buildHierarchy(Relation<AtomicConcept> hierarchyRelation) {
		////
		System.out.println("entering method buildHierarchy in TailoredQuasiOrderClassification");
		////
		double totalNumberOfTasks=m_upperBoundSubsumptions.keySet().size();
		makeConceptUnsatisfiable(m_bottomElement);
		initialiseKnownSubsumptionsUsingLowerBoundProvided();
		
		//for every class that isn't potentially unsatisfiable, register its possible subsumers, for every class that is, build a model to check its status.
		initialisePossibleSubsumptionsUsingUpperBoundProvided();
		
		////
		long t = System.currentTimeMillis();
		////
		
		//this method builds a model for every node representant in the explicit hierarchy obtained in initialiseKnownSubsumptionsUsingLowerBoundProvided(); 
		double tasksPerformed = updateSubsumptionsUsingLeafNodeStrategy(totalNumberOfTasks); 
		
		////
		t = System.currentTimeMillis() - t;
		System.out.println(t + " ms to updateSubsumptionsUsingLeafNodeStrategy ");
		////
		
		
		// Unlike Rob's paper our set of possible subsumptions P would only keep unknown possible subsumptions and not known subsumptions as well.
		
		
		//Here it's first checked whether the element is satisfiable in order to also retrieve known subsumers from the hypertableau
		//If after retrieving this there are still candidate subsumptions left then it's added to unclassifiedElements to be further studied in the next phase
		Set<AtomicConcept> unclassifiedElements=new HashSet<AtomicConcept>();
		
		///
		 t = System.currentTimeMillis();
		///
		 
		for (AtomicConcept element : m_upperBoundSubsumptions.keySet()) {
			if (!isUnsatisfiable(element)) {
				m_possibleSubsumptions.getSuccessors(element).removeAll(getAllKnownSubsumers(element));
				if (!m_possibleSubsumptions.getSuccessors(element).isEmpty()) {
					unclassifiedElements.add(element);
					continue;
				}
			}
		}
		
		////
		t = System.currentTimeMillis() - t;
		System.out.println(t + " ms for the satisfiability test");
		System.out.println(unclassifiedElements.size() + "/" + m_upperBoundSubsumptions.keySet().size() + " elements not fully classified after the satisfiability test" );
		if (unclassifiedElements.size() < 100)
			System.out.println(unclassifiedElements.toString());
		////
		
		Set<AtomicConcept> classifiedElements=new HashSet<AtomicConcept>();
		while (!unclassifiedElements.isEmpty()) {
			AtomicConcept unclassifiedElement=null;
			for (AtomicConcept element : unclassifiedElements) {
				m_possibleSubsumptions.getSuccessors(element).removeAll(getAllKnownSubsumers(element));
				if (!m_possibleSubsumptions.getSuccessors(element).isEmpty()) {
					unclassifiedElement=element;
					break;
				}
				classifiedElements.add(element);
				while (unclassifiedElements.size()<(totalNumberOfTasks-tasksPerformed)) {
					m_progressMonitor.elementClassified(element);
					tasksPerformed++;
				}
			}
			unclassifiedElements.removeAll(classifiedElements);
			if (unclassifiedElements.isEmpty())
				break;
			Set<AtomicConcept> unknownPossibleSubsumers=m_possibleSubsumptions.getSuccessors(unclassifiedElement);
			
//			///
//			System.out.println("going to classify " + unclassifiedElement.toString());
//			///
			
			t = System.currentTimeMillis();
			
			if (!isEveryPossibleSubsumerNonSubsumer(unknownPossibleSubsumers,unclassifiedElement,2,7) && !unknownPossibleSubsumers.isEmpty()) {
				Hierarchy<AtomicConcept> smallHierarchy=buildHierarchyOfUnknownPossible(unknownPossibleSubsumers);
				checkUnknownSubsumersUsingEnhancedTraversal(hierarchyRelation,smallHierarchy.getTopNode(),unclassifiedElement);
			}
//			//
//			else
//				System.out.println("every poss subsumer for " + unclassifiedElement.toString() + " is not a subsumer");
//			
//			t = System.currentTimeMillis() - t;
//			System.out.println(t + "ms to classify " + unclassifiedElement.toString());
//			System.out.println(unclassifiedElements.size() + " classes left to classify");
//			//
			
			unknownPossibleSubsumers.clear();
		}
		return buildTransitivelyReducedHierarchy(m_knownSubsumptions,m_elements);
	}
	protected double updateSubsumptionsUsingLeafNodeStrategy(double totalNumberOfTasks) {
		
		//We don't need to process here any nodes not found to be potentially unsatisfiable
		//the method conceptHasBeenProcessedAlready(...) will make sure of that
		
		double conceptsProcessed = 0;
		Hierarchy<AtomicConcept> hierarchy=buildTransitivelyReducedHierarchy(m_knownSubsumptions,m_elements);
		Stack<HierarchyNode<AtomicConcept>> toProcess=new Stack<HierarchyNode<AtomicConcept>>();
		toProcess.addAll(hierarchy.getBottomNode().getParentNodes());
		Set<HierarchyNode<AtomicConcept>> unsatHierarchyNodes=new HashSet<HierarchyNode<AtomicConcept>>();
		
		///
		int n = 0;
		///
		
		while (!toProcess.empty()) {
			HierarchyNode<AtomicConcept> currentHierarchyElement=toProcess.pop();
			AtomicConcept currentHierarchyConcept=currentHierarchyElement.getRepresentative();
			if (conceptsProcessed < Math.ceil(totalNumberOfTasks*0.85)) {
				m_progressMonitor.elementClassified(currentHierarchyConcept);
				conceptsProcessed++;
			}
			if (conceptIsPotentiallyUnsatisfiable(currentHierarchyConcept)) {
				
				///
				System.out.println(currentHierarchyConcept.toString());
				n++;
				///
				
				Node rootNodeOfModel=buildModelForConcept(currentHierarchyConcept);
				if (rootNodeOfModel==null) {
					makeConceptUnsatisfiable(currentHierarchyConcept);
					unsatHierarchyNodes.add(currentHierarchyElement);
					toProcess.addAll(currentHierarchyElement.getParentNodes());
					Set<HierarchyNode<AtomicConcept>> visited=new HashSet<HierarchyNode<AtomicConcept>>();
					Queue<HierarchyNode<AtomicConcept>> toVisit=new LinkedList<HierarchyNode<AtomicConcept>>(currentHierarchyElement.getChildNodes());
					while (!toVisit.isEmpty()) {
						HierarchyNode<AtomicConcept> current=toVisit.poll();
						if (visited.add(current) && !unsatHierarchyNodes.contains(current)) {
							toVisit.addAll(current.getChildNodes());
							unsatHierarchyNodes.add(current);
							makeConceptUnsatisfiable(current.getRepresentative());
							toProcess.remove(current);
							for (HierarchyNode<AtomicConcept> parentOfRemovedConcept : current.getParentNodes())
								if (conceptIsPotentiallyUnsatisfiable(parentOfRemovedConcept.getRepresentative()))
									toProcess.add(parentOfRemovedConcept);
						}
					}
				}
				else {
					// We cannot do rootNodeOfModel.getCanonicalNode() here. This is done
					// in readKnownSubsumersFromRootNode(), but only if rootNodeOfModel
					// has not been merged into another node, or if the merge was deterministic.
					readKnownSubsumersFromRootNode(currentHierarchyConcept,rootNodeOfModel);
					updatePossibleSubsumers();
				}
			}
		}
		
		System.out.println(n);
		
		return conceptsProcessed;
	}
	 protected boolean conceptIsPotentiallyUnsatisfiable(AtomicConcept atConcept) {
		 Set<AtomicConcept> aux = m_possibleSubsumptions.getSuccessors(atConcept);
		 return (aux.size() == 1 && aux.iterator().next().equals(AtomicConcept.NOTHING));
	 }
	// protected void readKnownSubsumersFromRootNode(AtomicConcept subconcept,Node checkedNode) {
	//     if (checkedNode.getCanonicalNodeDependencySet().isEmpty()) {
	//         checkedNode=checkedNode.getCanonicalNode();
	//         ExtensionTable.Retrieval retrieval=m_tableau.getExtensionManager().getBinaryExtensionTable().createRetrieval(new boolean[] { false,true },ExtensionTable.View.TOTAL);
	//         retrieval.getBindingsBuffer()[1]=checkedNode;
	//         retrieval.open();
	//         while (!retrieval.afterLast()) {
	//             Object conceptObject=retrieval.getTupleBuffer()[0];
	//             if (conceptObject instanceof AtomicConcept && retrieval.getDependencySet().isEmpty() && m_elements.contains(conceptObject))//no need to change this m_elements into m_elementsToClassify since concept is a candidate subsumER
	//                 addKnownSubsumption(subconcept,(AtomicConcept)conceptObject);
	//             retrieval.next();
	//         }
	//     }
	// }
	@Override
	protected void updatePossibleSubsumers() {
		ExtensionTable.Retrieval retrieval=m_tableau.getExtensionManager().getBinaryExtensionTable().createRetrieval(new boolean[] { false,false },ExtensionTable.View.TOTAL);
		retrieval.open();
		Object[] tupleBuffer=retrieval.getTupleBuffer();
		while (!retrieval.afterLast()) {
			Object conceptObject=tupleBuffer[0];
			if (conceptObject instanceof AtomicConcept ){ // && m_upperBoundSubsumptions.keySet().contains(conceptObject)) {////we can probably remove the &&... given the current implementation of buildHierarchy 
				AtomicConcept atomicConcept=(AtomicConcept)conceptObject;
				Node node=(Node)tupleBuffer[1];
				if (node.isActive() && !node.isBlocked()) {
					if (m_possibleSubsumptions.getSuccessors(atomicConcept).isEmpty())
						readPossibleSubsumersFromNodeLabel(atomicConcept,node);
					else
						prunePossibleSubsumersOfConcept(atomicConcept,node);
				}
			}
			retrieval.next();
		}
	}
	@Override
	protected void prunePossibleSubsumers() {//used inside updateSubsumptionsUsingLeafNodeStrategy(int)
		ExtensionTable.Retrieval retrieval=m_tableau.getExtensionManager().getBinaryExtensionTable().createRetrieval(new boolean[] { false,false },ExtensionTable.View.TOTAL);
		retrieval.open();
		Object[] tupleBuffer=retrieval.getTupleBuffer();
		while (!retrieval.afterLast()) {
			Object conceptObject=tupleBuffer[0];
			if (conceptObject instanceof AtomicConcept && m_upperBoundSubsumptions.keySet().contains(conceptObject)) {
				Node node=(Node)tupleBuffer[1];
				if (node.isActive() && !node.isBlocked())
					prunePossibleSubsumersOfConcept((AtomicConcept)conceptObject,node);
			}
			retrieval.next();
		}
	}
//	@Override 
//	protected void prunePossibleSubsumersOfConcept(AtomicConcept atomicConcept,Node node) {
//		//same as in superclass but was not visible
//        Set<AtomicConcept> possibleSubsumersOfConcept=new HashSet<AtomicConcept>(m_possibleSubsumptions.getSuccessors(atomicConcept));
//        for (AtomicConcept atomicCon : possibleSubsumersOfConcept)
//            if (!m_tableau.getExtensionManager().containsConceptAssertion(atomicCon,node))
//                m_possibleSubsumptions.getSuccessors(atomicConcept).remove(atomicCon);
//    }
	// protected void readPossibleSubsumersFromNodeLabel(AtomicConcept atomicConcept,Node node) {
	//     ExtensionTable.Retrieval retrieval=m_tableau.getExtensionManager().getBinaryExtensionTable().createRetrieval(new boolean[] { false,true },ExtensionTable.View.TOTAL);
	//     retrieval.getBindingsBuffer()[1]=node;
	//     retrieval.open();
	//     while (!retrieval.afterLast()) {
	//         Object concept=retrieval.getTupleBuffer()[0];
	//         if (concept instanceof AtomicConcept && m_elements.contains(concept))//no need to change this m_elements into m_elementsToClassify since concept is a candidate subsumER
	//             addPossibleSubsumption(atomicConcept,(AtomicConcept)concept);
	//         retrieval.next();
	//     }
	// }

	protected void initialiseKnownSubsumptionsUsingLowerBoundProvided() {
		//Any told subsumptions in the ontology must already have been identified in the lower bound that we provide to HermiT, so let's process this lower bound here instead of calling init...UsingToldSubsumers  
		for (AtomicConcept ac : m_lowerBoundSubsumptions.keySet())
			for (AtomicConcept sup : m_lowerBoundSubsumptions.get(ac))
				addKnownSubsumption(ac,sup);	
	}
	
	protected void initialisePossibleSubsumptionsUsingUpperBoundProvided() {
		
//		//is m_possibleSubsumptions empty before this? 
//		System.out.println(m_possibleSubsumptions.)
		
		//Any told subsumptions in the ontology must already have been identified in the lower bound that we provide to HermiT, so let's process this lower bound here instead of calling init...UsingToldSubsumers
//		AtomicConcept bot = AtomicConcept.NOTHING;
//		AtomicConcept bot2 = AtomicConcept.create("owl:Nothing");
		//////would probably be faster to do this iterating directly over entries - TODO
		for (Entry<AtomicConcept, Collection<AtomicConcept>> entry : m_upperBoundSubsumptions.entrySet()){
//			if (!entry.getValue().contains(bot))
				for (AtomicConcept sup : entry.getValue())
					addPossibleSubsumption(entry.getKey(),sup);
				
				//check that the potential unsatisfiability of this concept has been registered
				//--TODO				
		}
	}
}