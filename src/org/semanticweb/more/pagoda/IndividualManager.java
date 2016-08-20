package org.semanticweb.more.pagoda;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.semanticweb.HermiT.model.Individual;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.more.util.PrintingUtility;
import org.semanticweb.more.util.Utility;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;
import uk.ac.ox.cs.pagoda.util.Namespace;

public class IndividualManager {

//	boolean inyectiveSkolemisation;
//	int skolemisationIndividualCounter = 0;
//	Map<DLClause, Integer> index4clause = new HashMap<DLClause, Integer>();
	
//	boolean inyectiveInstantiation;
	int instantiationIndividualCounter = 0;
	Map<OWLClass, Integer> index4Class;
	Map<Integer, OWLClass> class4Index;
	List<Integer> activeIndexes; //indexes 4 classes that are not fully classified yet
	List<Integer> inactiveIndexes;
//	Map<OWLObjectProperty, Integer> index4Property;
	
//	static Individual criticalInstance;
	
	static final String freshIndividualPrefix = MyNamespace.TM_ANONY + "instantiation";

	
	public IndividualManager() {
		index4Class = new HashMap<OWLClass, Integer>();
		class4Index = new HashMap<Integer, OWLClass>();
		activeIndexes = new LinkedList<Integer>();
		inactiveIndexes = new LinkedList<Integer>();
	}
	
	public int getNoInstantiationIndividuals(){
		return instantiationIndividualCounter;
	}
	
	public void printTopFactsForAllIndividuals(PrintWriter facts) throws Exception{
		OWLClass top = new OWLDataFactoryImpl().getOWLThing();
		for (Entry<OWLClass, Integer> e : index4Class.entrySet()){
			PrintingUtility.print(facts, top,getInstanceIndividualForIndex(e.getValue()));
		}
	}
	public Individual getInstanceIndividual(OWLEntity e, boolean createIfNotAlreadyExists){
		Integer i = getIndex4Entity(e);
		if (i != null)
			return getInstanceIndividualForIndex(i);
		else if (createIfNotAlreadyExists){
			i = assignFreshInstanceIndividual(e);
			return getInstanceIndividualForIndex(i);
		}
		else
			return null;
	}
	
	protected Integer getIndex4Entity(OWLEntity e){//instantiation
		if (e instanceof OWLClass)
			return index4Class.get((OWLClass) e);
		else throw new IllegalArgumentException(e.toString());
	}
	
	public OWLClass getClass4Individual(OWLIndividual i){
		return getClass4Individual(i.toString());
	}

	protected Integer extractIndex(String ind){
		try{
			Integer index = Integer.parseInt(ind.replace(freshIndividualPrefix, "").replace("<", "").replace(">", ""));
			return index;
		}catch (NumberFormatException e){
			return null;
		}
	}
	
	public OWLClass getClass4Individual(String i){
		Integer index = extractIndex(i);
		if (index != null)
			return class4Index.get(index);
		else
			return null;
	}

	protected Integer assignFreshInstanceIndividual(OWLEntity e){
		Integer i = instantiationIndividualCounter;
		if (e instanceof OWLClass){
			index4Class.put((OWLClass) e, i);
			class4Index.put(i, (OWLClass) e);
			activeIndexes.add(i);
		}
		else throw new IllegalArgumentException();
		instantiationIndividualCounter++;
		return i;
	}
	
	public Individual getInstanceIndividualForIndex(Integer i){
		return Individual.create(freshIndividualPrefix + i);
	}
	
	public static boolean isInstantiationIndividual(String s){
		return s.contains(freshIndividualPrefix);
	}
	
	public boolean isIndividual4ClassToClassify(String i){
		if (!isInstantiationIndividual(i))
			return false;
		Integer index = extractIndex(i);
		if (activeIndexes.size() > inactiveIndexes.size())
			return !inactiveIndexes.contains(index);
		else
			return activeIndexes.contains(index);
	}
	
	public void updateActiveIndexes(Collection<String> individualsWithGap){
		inactiveIndexes.addAll(activeIndexes);
		activeIndexes.clear();
		for (String s : individualsWithGap){
			Integer i = extractIndex(s);
			if (i != null) {
				activeIndexes.add(i);
				inactiveIndexes.remove(i);
			}
			else
				Logger_MORe.logError("problem updating activeIndexes");
		}
		
		Logger_MORe.logInfo("There are " + activeIndexes.size() + " classes still not completely classified");
//		////
//		for (String s : individualsWithGap)
//			System.out.println(s);
//		////
	}

	public void registerFullyClassifiedClasses(
			List<String> individuals4unsatClasses) {
		for (String s : individuals4unsatClasses){
			Integer i = extractIndex(s);
			if (i != null){
				activeIndexes.remove(i);
				inactiveIndexes.add(i);
			}
			else
				Logger_MORe.logError("problem updating activeIndexes");
		}
		Logger_MORe.logInfo("There are " + activeIndexes.size() + " classes still not completely classified");
	}

	
	protected OWLOntology rewriteABoxAxiomsAsTBoxAxioms(OWLOntology o) throws OWLOntologyCreationException{
		
//		for (OWLAxiom ax : o.getAxioms())
//			System.out.println(ax.toString());
//		System.out.println();
		
		
        OWLDataFactory factory = new OWLDataFactoryImpl();
        OWLOntologyManager manager = o.getOWLOntologyManager();
        OWLOntology ret = manager.createOntology(IRI.create(Utility.getOntologyID_ontologyForOWL2Reasoner()));
        for (OWLAxiom ax : o.getAxioms()){
        	if (ax instanceof OWLClassAssertionAxiom){
        		if (isInstantiationIndividual(((OWLClassAssertionAxiom) ax).getIndividual().toString())){
        			OWLClass superClass = (OWLClass) ((OWLClassAssertionAxiom) ax).getClassExpression();
        			OWLIndividual ind = ((OWLClassAssertionAxiom) ax).getIndividual();
        			OWLClass subClass = getClass4Individual(ind);
        			if (!superClass.equals(subClass) && !superClass.isOWLThing()){
        				OWLAxiom newAx = factory.getOWLSubClassOfAxiom(subClass, superClass); 
        				manager.addAxiom(ret, newAx);
        			}
        		}
        	}
        	else if (ax instanceof OWLObjectPropertyAssertionAxiom){
        		Logger_MORe.logError("This is weird, a role assertion in the lower bound??? " + ax.toString());
            }
            else
            	manager.addAxiom(ret, ax);
        }
        Logger_MORe.logInfo("after rewriting ABox axioms as TBox axioms the returned ontology contains " + ret.getAxiomCount() + " axioms");
        
        
//        for (OWLAxiom ax : ret.getAxioms())
//			System.out.println(ax.toString());
//		System.out.println();
        
		
		return ret;    
    }
	public class MyNamespace extends Namespace{
		
		public static final String TM_ANONY = "http://www.cs.ox.ac.uk/MORe#";
	 
	}


}
