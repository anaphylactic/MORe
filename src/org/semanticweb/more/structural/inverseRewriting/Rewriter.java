package org.semanticweb.more.structural.inverseRewriting;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLIndividualAxiom;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLPropertyAxiom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectAllValuesFromImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectSomeValuesFromImpl;
//import carral.OntologyEvaluator;
//import carral.Shared;

public class Rewriter{
	Set<OWLAxiom> axioms;
	Set<SortedGCI> sorted;
    protected final OWLDataFactory m_factory=new OWLDataFactoryImpl();
    static int freshClassCounter=0;
//	Set<SortedGCI> gcis;
//	Collection<OWLIndividualAxiom> facts;
//	Collection<OWLPropertyAxiom> roles;

	public Rewriter(Set<OWLAxiom> axioms, Set<SortedGCI> sorted){
		this.axioms = axioms;
		this.sorted = sorted;
//		this.facts =ontology.getFacts();
//		this.roles =ontology.getPropertyAxioms();
	}
	
	
	
	
	static boolean hasNominals(Set<SortedGCI> sorted){
		for (SortedGCI gci:sorted)
			if (!gci.rhsOneof.isEmpty()) return true;
		return false;
	}
	
	
	public Set<OWLAxiom> getRewrittenOntology() {
		Set<OWLAxiom> gcis=new HashSet<OWLAxiom>();
		Set<OWLAxiom> interm=new HashSet<OWLAxiom>();
		Set<OWLAxiom> result=new HashSet<OWLAxiom>();
		
	    Collection<OWLPropertyAxiom> propertyAxioms=new HashSet<OWLPropertyAxiom>();
	    		propertyAxioms.addAll(RoleOperations.getPropertyAxioms(axioms));
		
		Set<OWLObjectPropertyExpression> nonRewr=RoleOperations.getNonRewritableRoles(axioms, hasNominals(sorted)) ;
		Logger_MORe.logDebug(nonRewr.size()+"non-rewritable roles in the rewritten");
		
		gcis=rewriteGCIs(sorted, nonRewr);
		Logger_MORe.logDebug("Rewriting GCIs Done");
		
		//this is needed just to compute the set of active roles
		interm.addAll(gcis);
		interm.addAll(propertyAxioms);
		Set<OWLObjectPropertyExpression> active=RoleOperations.getActiveRoles(interm);
				
		//constructing the result
		result.addAll(gcis);
		result.addAll(rewriteProperties(propertyAxioms, active, nonRewr));
		Logger_MORe.logDebug("Rewriting Properties Done");
		Logger_MORe.logDebug("Facts:" + RoleOperations.getAssertionAxioms(axioms).size());
		result.addAll(rewriteFacts(RoleOperations.getAssertionAxioms(axioms), active, nonRewr));
		Logger_MORe.logDebug("Rewriting Facts Done");
		
		return (result); 
	}
	
	
	public Set<OWLAxiom> rewritePropertiesSimple(Collection<OWLPropertyAxiom> propIncs, Set<OWLObjectPropertyExpression> active, Set<OWLObjectPropertyExpression> nonRewr) {
		Set<OWLAxiom> interm= new HashSet<OWLAxiom>();
		
		for (OWLPropertyAxiom propInc:propIncs)
		{
			OWLSubObjectPropertyOfAxiom subProp = (OWLSubObjectPropertyOfAxiom) propInc;
			OWLObjectPropertyExpression lprop=subProp.getSubProperty();
			OWLObjectPropertyExpression rprop=subProp.getSuperProperty();
				interm.add(m_factory.getOWLSubObjectPropertyOfAxiom(RoleOperations.getNewRoleName(lprop.getInverseProperty().getSimplified(), nonRewr), 
						RoleOperations.getNewRoleName(rprop.getInverseProperty().getSimplified(), nonRewr)));  
				interm.add(m_factory.getOWLSubObjectPropertyOfAxiom(RoleOperations.getNewRoleName(lprop, nonRewr), RoleOperations.getNewRoleName(rprop, nonRewr)));
		}
		return interm; 		
	}
			
	public Set<OWLAxiom> rewriteProperties(Collection<OWLPropertyAxiom> propIncs, Set<OWLObjectPropertyExpression> active, Set<OWLObjectPropertyExpression> nonRewr) {
		Set<OWLAxiom> interm= new HashSet<OWLAxiom>();
		
		for (OWLPropertyAxiom propInc:propIncs){
			OWLSubObjectPropertyOfAxiom subProp = (OWLSubObjectPropertyOfAxiom) propInc;
			OWLObjectPropertyExpression lprop=subProp.getSubProperty();
			OWLObjectPropertyExpression rprop=subProp.getSuperProperty();
			if (active.contains(rprop.getInverseProperty().getSimplified()))  
				interm.add(m_factory.getOWLSubObjectPropertyOfAxiom(RoleOperations.getNewRoleName(lprop.getInverseProperty().getSimplified(), nonRewr), 
						RoleOperations.getNewRoleName(rprop.getInverseProperty().getSimplified(), nonRewr)));
			if (active.contains(rprop))  
				interm.add(m_factory.getOWLSubObjectPropertyOfAxiom(RoleOperations.getNewRoleName(lprop, nonRewr), RoleOperations.getNewRoleName(rprop, nonRewr)));
//			if (!active.contains(rprop.getInverseProperty().getSimplified())&&!active.contains(rprop)) System.out.println("Nada:"+propInc);
		}
		return interm; 		
	}
	
	
	public Set<OWLAxiom> rewriteFacts(Collection<OWLIndividualAxiom> facts, Set<OWLObjectPropertyExpression> active, Set<OWLObjectPropertyExpression> nonRewr) {
		Set<OWLAxiom> interm= new HashSet<OWLAxiom>();
		for (OWLIndividualAxiom fact:facts)
			if (fact.isOfType(AxiomType.CLASS_ASSERTION)||fact.isOfType(AxiomType.DIFFERENT_INDIVIDUALS)||fact.isOfType(AxiomType.SAME_INDIVIDUAL)) {
			//	System.out.println("Class Assertion");
				interm.add(fact);
			}
			else 			
		{
				OWLObjectPropertyAssertionAxiom axiom=(OWLObjectPropertyAssertionAxiom) fact;
				OWLObjectPropertyExpression prop= axiom.getProperty();
				OWLIndividual object= axiom.getObject();
				OWLIndividual subject= axiom.getSubject();
//				if (active.contains(prop.getInverseProperty().getSimplified())&&!nonRewr.contains(prop.getInverseProperty().getSimplified()))  
//					interm.add(m_factory.getOWLObjectPropertyAssertionAxiom(RoleOperations.getNewRoleName(prop.getInverseProperty().getSimplified(), nonRewr), 
//							 object, subject));
//				if (active.contains(prop)||nonRewr.contains(prop.getInverseProperty().getSimplified()))  
//					interm.add(fact);
				
				if (active.contains(prop.getInverseProperty().getSimplified()))  
					interm.add(m_factory.getOWLObjectPropertyAssertionAxiom(RoleOperations.getNewRoleName(prop.getInverseProperty().getSimplified(), nonRewr), 
							 object, subject));
				if (active.contains(prop)) 
					interm.add(fact);
				
		    interm.add(m_factory.getOWLObjectPropertyAssertionAxiom(prop, subject, object));
		}
		
		return interm; 		
	}
	
	public Set<OWLAxiom> rewriteGCIs(Set<SortedGCI> gcis, Set<OWLObjectPropertyExpression> nonRewr){
//		ArrayList<OWLClassExpression> lhs=new ArrayList<OWLClassExpression>();
//		ArrayList<OWLClassExpression> rhs=new ArrayList<OWLClassExpression>();
		//I've commented these out because they were only being filled but never used
		
		Set<OWLObjectPropertyExpression> generating=RoleOperations.getGeneratingRoles(axioms);
		Set<OWLAxiom> interm= new HashSet<OWLAxiom>();
//		int i=0;
		for (SortedGCI gci:gcis)
		{
//			lhs.addAll(gci.lhsExistential);
			if (gci.lhsAtomic.size()+gci.lhsExistential.size()==0) 
				gci.lhsAtomic.add(m_factory.getOWLThing()); 
//			lhs.addAll(gci.lhsAtomic);
//			rhs.addAll(gci.rhsUniversal);
//			rhs.addAll(gci.rhsExistential);
//			rhs.addAll(gci.rhsMaxCard);
//			rhs.addAll(gci.rhsOneof);
	    	if (gci.rhsAtomic.size()+gci.rhsExistential.size()+gci.rhsMaxCard.size()+gci.rhsOneof.size()+gci.rhsUniversal.size()==0) 
	    		gci.rhsAtomic.add(m_factory.getOWLNothing());
//			rhs.addAll(gci.rhsAtomic);			
			//System.out.println("GCI Rewritten:"+(i++)+GCIrewriteNonRec(gci, generating, nonRewr));
			Set<OWLSubClassOfAxiom> partialRW=GCIrewriteNonRec(gci, generating, nonRewr);
			if (partialRW.isEmpty()) 
				System.out.println(gci);
			else
				interm.addAll(partialRW);

		}
		return interm; 		
	}
	
	
	
	private OWLSubClassOfAxiom rewriteSortedGCI(SortedGCI sorted, Set<OWLObjectPropertyExpression> nonRW){
		Set<OWLSubClassOfAxiom> newaxioms=new HashSet<OWLSubClassOfAxiom>();
		Set<OWLClassExpression> c= new HashSet<OWLClassExpression>();
		Set<OWLClassExpression> d= new HashSet<OWLClassExpression>();
		
		Set<OWLClassExpression> newC= new HashSet<OWLClassExpression>();
		Set<OWLClassExpression> newD= new HashSet<OWLClassExpression>();
		
		OWLClassExpression lhs;
		OWLClassExpression rhs;
		
		RoleRewriter visitor=new RoleRewriter(nonRW);
		
		c.addAll(sorted.lhsAtomic);
		c.addAll(sorted.lhsExistential);
		if (c.isEmpty()) c.add(m_factory.getOWLThing());
		

		d.addAll(sorted.rhsAtomic);
		d.addAll(sorted.rhsExistential);
		d.addAll(sorted.rhsMaxCard);
		d.addAll(sorted.rhsOneof);
		d.addAll(sorted.rhsUniversal);
		if (d.isEmpty()) d.add(m_factory.getOWLNothing());
		//if (c.toString().concat(d.toString()).contains("accomplishment")) System.out.println("Sorted GCI"+sorted.toString());
	
		
		for (OWLClassExpression ci:c){
			ci.accept(visitor);
			newC.add(visitor.newClass);
		}
		if (c.size()>1) lhs=m_factory.getOWLObjectIntersectionOf(newC);
		else lhs=visitor.newClass;
		
		for (OWLClassExpression di:d){ 
			di.accept(visitor);
			newD.add(visitor.newClass);
		}
		if (d.size()>1) rhs=m_factory.getOWLObjectUnionOf(newD);
		else rhs=visitor.newClass;
		
		
	return(m_factory.getOWLSubClassOfAxiom(lhs, rhs));
//	System.out.println("Rewritten GCI:"+m_factory.getOWLSubClassOfAxiom(lhs, rhs).toString());

	}
	
	
	
	private OWLSubClassOfAxiom rewriteGCI(ArrayList<OWLClassExpression> c,  ArrayList<OWLClassExpression> d, Set<OWLObjectPropertyExpression> nonRW){
//		System.out.println("Original GCI left:"+c.toString());
//		System.out.println("Original GCI right:"+d.toString());
//		Set<OWLSubClassOfAxiom> newaxioms=new HashSet<>();
		Set<OWLClassExpression> newC= new HashSet<OWLClassExpression>();
		Set<OWLClassExpression> newD= new HashSet<OWLClassExpression>();
		OWLClassExpression lhs;
		OWLClassExpression rhs;
		
//		System.out.println("Processed GCI left:"+c.toString());
//		System.out.println("Processed GCI right:"+d.toString());
//		System.out.println();
//		System.in.read();
		
		RoleRewriter visitor=new RoleRewriter(nonRW); 
		
		if (c.isEmpty()) c.add(m_factory.getOWLThing());
		for (OWLClassExpression ci:c){
			ci.accept(visitor);
			newC.add(visitor.newClass);
		}
		
		//if (c.toString().contains("accomplishment")) System.out.println("GCI left:"+c.toString());
		if (c.size()>1) lhs=m_factory.getOWLObjectIntersectionOf(newC);
		else lhs=(OWLClassExpression) newC.toArray()[0];
	//	visitor.newClass;
		
		if (d.isEmpty()) d.add(m_factory.getOWLNothing());
		for (OWLClassExpression di:d){ 
			di.accept(visitor);
			newD.add(visitor.newClass);
		}
		
//		if (c.toString().concat(d.toString()).contains("accomplishment")) System.out.println("GCI"+c.toString()+"   "+d.toString());
		if (d.size()>1) rhs=m_factory.getOWLObjectUnionOf(newD);
		else rhs=(OWLClassExpression) newD.toArray()[0];
		OWLSubClassOfAxiom newAxiom= m_factory.getOWLSubClassOfAxiom(lhs, rhs);
return newAxiom;
	}
	
	
	private Set<OWLSubClassOfAxiom> GCIrewriteNonRec(SortedGCI gci,  Set<OWLObjectPropertyExpression> generatingRoles, Set<OWLObjectPropertyExpression> nonRW){
//	java.util.List<java.util.Map.Entry<ArrayList<OWLClassExpression>,ArrayList<OWLClassExpression>>> newaxioms= new java.util.ArrayList<>();
		if (gci.lhsAtomic.size()+gci.lhsExistential.size()>1 && gci.lhsAtomic.contains(m_factory.getOWLThing()))  gci.lhsAtomic.remove(m_factory.getOWLThing());
		if (gci.rhsAtomic.size()+gci.rhsExistential.size()+gci.rhsMaxCard.size()+gci.rhsOneof.size()+gci.rhsUniversal.size()>1 && gci.rhsAtomic.contains(m_factory.getOWLNothing()))  gci.rhsAtomic.remove(m_factory.getOWLNothing());
		
	Set<OWLSubClassOfAxiom> newaxioms=new HashSet<OWLSubClassOfAxiom>(); 
	ArrayList<OWLClassExpression> templeft= new java.util.ArrayList<OWLClassExpression>();
	ArrayList<OWLClassExpression> tempright= new java.util.ArrayList<OWLClassExpression>();
		
	ArrayList<OWLObjectSomeValuesFrom> refExist=(ArrayList<OWLObjectSomeValuesFrom>) gci.lhsExistential.clone();
	ArrayList<OWLObjectAllValuesFrom> refUniv=(ArrayList<OWLObjectAllValuesFrom>) gci.rhsUniversal.clone();
//	System.out.println("Original Sorted GCI:"+ gci.toString());
	int existsize=refExist.size();
	int univsize=refUniv.size();
	boolean processed=false;

	if (existsize+univsize>0)
		for (int i=0; i<existsize+univsize; i++){
			if (i<existsize){ //still some l.h.s existential to be processed 
			//	System.out.println("refExistsize:"+refExist.size());
				OWLObjectSomeValuesFrom exists=refExist.get(i);
				OWLObjectPropertyExpression role = exists.getProperty();
				OWLClassExpression filler = exists.getFiller();
			    if (generatingRoles.contains(role.getInverseProperty().getSimplified())){
				if (gci.lhsExistential.size()==1 &&  gci.rhsExistential.size()+gci.rhsMaxCard.size()+gci.rhsUniversal.size()==0 && 
						gci.lhsAtomic.size()+gci.rhsAtomic.size()<2)
				{
					 	processed=true;
					 	if (generatingRoles.contains(role)) newaxioms.add(rewriteSortedGCI(gci, nonRW)); //add the original GCI
					 	
						if (gci.rhsAtomic.size()==1){ //the case: exists R.A \sqcap \sqs B, 		
							templeft.add(filler);
							tempright.add(new OWLObjectAllValuesFromImpl(role.getInverseProperty().getSimplified(), gci.rhsAtomic.get(0)));
							//adding A \sqcap \forall inv(R).B/ \bottom
							newaxioms.add(rewriteGCI(templeft, tempright, nonRW));
							templeft.clear(); tempright.clear();
							//further on, if R is generating, add the original axiom
//						    if (generatingRoles.contains(role)) //newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (c, d));
//						    	addAndRewriteGCI(newaxioms, (ArrayList<OWLClassExpression>)  gci.lhsExistential.get(0), (ArrayList<OWLClassExpression>) gci.rhsAtomic.get(0), nonRW);
					    }
						if (gci.rhsAtomic.size()==0&&gci.lhsAtomic.size()==0){ //the case: exists R.A \sqs \bottom, 	
							templeft.add(filler);
							tempright.add(new OWLObjectAllValuesFromImpl(role.getInverseProperty().getSimplified(), m_factory.getOWLNothing()));
							//adding A \sqcap \forall inv(R).B/ \bottom
							newaxioms.add(rewriteGCI(templeft, tempright, nonRW));
							templeft.clear(); tempright.clear();
							//further on, if R is generating, add the original axiom
//						    if (generatingRoles.contains(role)) //newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (c, d));
//						    	addAndRewriteGCI(newaxioms, (ArrayList<OWLClassExpression>)  gci.lhsExistential.get(0), (ArrayList<OWLClassExpression>) m_factory.getOWLNothing(), nonRW);
						    }
						//the case: exists R.A \sqcap B \sqs \bottom,
						if (gci.lhsAtomic.size()==1){
							templeft.add(filler);
							templeft.add(new OWLObjectSomeValuesFromImpl(role.getInverseProperty().getSimplified(), gci.lhsAtomic.get(0)));
							newaxioms.add(rewriteGCI(templeft, (ArrayList<OWLClassExpression>) m_factory.getOWLNothing(), nonRW));
							templeft.clear();
							//further on, if R is generating, add the original axiom
//						    if (generatingRoles.contains(role)) //newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (c, d));
//						    {
//						    	templeft.addAll(gci.lhsAtomic);
//						    	templeft.addAll(gci.lhsExistential);
//						    	addAndRewriteGCI(newaxioms, templeft, (ArrayList<OWLClassExpression>) m_factory.getOWLNothing(), nonRW);
//						    	templeft.clear();
						    }	
						}
				//the case where the existential has to be isolated (Inv(R) is generating)
				else{
					OWLClass x = OWLManager.getOWLDataFactory().getOWLClass(IRI.create("internal:def#rew" + freshClassCounter++));
					gci.lhsExistential.remove(exists);
					gci.lhsAtomic.add(x);
//					
					//adding A \sqcap \forall inv(R).X
					templeft.add(filler);
					tempright.add(new OWLObjectAllValuesFromImpl(exists.getProperty().getInverseProperty().getSimplified(), x));
					newaxioms.add(rewriteGCI(templeft, tempright, nonRW));
					templeft.clear();tempright.clear();

					//further on, if R is generating, add exists R.A \sqcap x 
					if (generatingRoles.contains(role)) //newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (templeft2, tempright2));
					{
						templeft.add(exists);
						tempright.add(x);
						newaxioms.add(rewriteGCI(templeft, tempright, nonRW));
					}
				}				
			}	
			}
			else if (!refUniv.isEmpty()) { //no l.h.s. existential needs to be processed, but there are some universals
				OWLObjectAllValuesFrom forall=refUniv.get(i-existsize);
				OWLObjectPropertyExpression role = forall.getProperty();
				OWLClassExpression filler = forall.getFiller();
				//inv(R) is generating or R is not
				if (generatingRoles.contains(role.getInverseProperty().getSimplified())||!generatingRoles.contains(role)) {
					if (gci.rhsUniversal.size()==1 &&  gci.rhsExistential.size()+gci.rhsMaxCard.size()+gci.lhsExistential.size()==0 && (gci.lhsAtomic.size()+gci.rhsAtomic.size())<2)
					{
						processed=true;
						if (generatingRoles.contains(role)) newaxioms.add(rewriteSortedGCI(gci, nonRW)); 
										
					if (gci.rhsAtomic.size()==1){ //the case: \top \sqs A \sqcup \forall R B, 		
						templeft.add(m_factory.getOWLThing());
						tempright.add(filler);
						tempright.add(new OWLObjectAllValuesFromImpl(role.getInverseProperty().getSimplified(), gci.rhsAtomic.get(0)));
						//adding A \sqcap \forall inv(R).B/ \bottom
						newaxioms.add(rewriteGCI(templeft, tempright, nonRW));
						templeft.clear(); tempright.clear();
						//further on, if R is generating, add the original axiom
//					    if (generatingRoles.contains(role)) //newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (c, d));
//					    	addAndRewriteGCI(newaxioms, (ArrayList<OWLClassExpression>)  gci.lhsExistential.get(0), (ArrayList<OWLClassExpression>) gci.rhsAtomic.get(0), nonRW);
				    }
					if (gci.rhsAtomic.size()==0&&gci.lhsAtomic.size()==0){ //the case: \top \sqs \forall R.A 	
						tempright.add(filler);
						templeft.add(new OWLObjectSomeValuesFromImpl(role.getInverseProperty().getSimplified(), m_factory.getOWLThing()));
						//adding A \sqcap \forall inv(R).B/ \bottom
						newaxioms.add(rewriteGCI(templeft, tempright, nonRW));
						templeft.clear(); tempright.clear();
						//further on, if R is generating, add the original axiom
//					    if (generatingRoles.contains(role)) //newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (c, d));
//					    	addAndRewriteGCI(newaxioms, (ArrayList<OWLClassExpression>)  gci.lhsExistential.get(0), (ArrayList<OWLClassExpression>) m_factory.getOWLNothing(), nonRW);
					    }
					//the case: A \sqs \forall R.B
					if (gci.lhsAtomic.size()==1){
						tempright.add(filler);
						templeft.add(new OWLObjectSomeValuesFromImpl(role.getInverseProperty().getSimplified(), gci.lhsAtomic.get(0)));
						newaxioms.add(rewriteGCI( templeft, tempright, nonRW));
						templeft.clear();
						//further on, if R is generating, add the original axiom
//					    if (generatingRoles.contains(role)) //newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (c, d));
//					    {
//					    	templeft.addAll(gci.lhsAtomic);
//					    	templeft.addAll(gci.lhsExistential);
//					    	addAndRewriteGCI(newaxioms, templeft, (ArrayList<OWLClassExpression>) m_factory.getOWLNothing(), nonRW);
//					    	templeft.clear();
					    }	
				}
					else// \forall R.A or the rest has to be isolated: 
					{ if (gci.rhsMaxCard.size()+gci.rhsUniversal.size()+gci.lhsAtomic.size()+gci.lhsExistential.size()>1){
					//renaming the universal 

						OWLClass x = OWLManager.getOWLDataFactory().getOWLClass(IRI.create("internal:def#rew" + freshClassCounter++));
						gci.rhsUniversal.remove(forall);
						gci.rhsAtomic.add(x);
//						
						//adding \exists inv(R).X \sqs A
						tempright.add(filler);
						templeft.add(new OWLObjectSomeValuesFromImpl(role.getInverseProperty().getSimplified(), x));
						newaxioms.add(rewriteGCI(templeft, tempright, nonRW));
						templeft.clear();tempright.clear();
		               
						//further on, if R is generating, add X \sqs \forall R.A 
						if (generatingRoles.contains(role)) //newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (templeft2, tempright2));
						{
							tempright.add(forall);
							templeft.add(x);
							newaxioms.add(rewriteGCI(templeft, tempright, nonRW));
					    	templeft.clear();tempright.clear();
						}	
				    }
					else{
						//replacing the rest of the disjunct with a new class name x
						OWLClass x = OWLManager.getOWLDataFactory().getOWLClass(IRI.create("internal:def#rew" + freshClassCounter++));
						gci.rhsUniversal.remove(forall);
						gci.lhsAtomic.add(x);
//						
						//adding \top \sqs \forall inv(R).X \sqcup A
						templeft.add(m_factory.getOWLThing()); 
						tempright.add(filler);
						tempright.add(new OWLObjectAllValuesFromImpl(role.getInverseProperty().getSimplified(), x));
						newaxioms.add(rewriteGCI(templeft, tempright, nonRW));
						templeft.clear();tempright.clear();
		               
						//further on, if R is generating, add \top \sqs X  \sqcup \forall R.A 
						if (generatingRoles.contains(role)) //newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (templeft2, tempright2));
						{
							templeft.add(m_factory.getOWLThing());
							tempright.add(forall);
							tempright.add(x);
							newaxioms.add(rewriteGCI(templeft, tempright, nonRW));
					    	templeft.clear();tempright.clear();
						}	
						
					}
			     }
			
		   }
		} 
	} 
	
	// end the big for
	//process the remaining GCI
	
	if (!processed) {
//		System.out.println("Remaining GCI lhsAtomic size:"+gci.lhsAtomic.size());
//		System.out.println("Remaining GCI rhsAtomic size:"+gci.rhsAtomic.size());
//		System.out.println("Remaining GCI lhsExistential size:"+gci.lhsExistential.size());
//		System.out.println("Remaining GCI rhsExistential size:"+gci.rhsExistential.size());
//		if (gci.rhsExistential.size()>0) System.out.println("Remaining GCI rhsExistential size:"+gci.rhsExistential.get(0));
//		System.out.println("Remaining GCI rhsMaxCardsize size:"+gci.rhsMaxCard.size());
//		System.out.println("Remaining GCI rhsUniversal size:"+gci.rhsUniversal.size());
//        System.in.read();
		newaxioms.add(rewriteSortedGCI(gci, nonRW));
	}
	return newaxioms;
	}		
	
	
//	private Set<OWLSubClassOfAxiom> GCIrewrite(ArrayList<OWLClassExpression> c,  ArrayList<OWLClassExpression> d,  Set<OWLObjectPropertyExpression> generatingRoles, Set<OWLObjectPropertyExpression> nonRW) throws IOException
//	{
////	java.util.List<java.util.Map.Entry<ArrayList<OWLClassExpression>,ArrayList<OWLClassExpression>>> newaxioms= new java.util.ArrayList<>();
//	Set<OWLSubClassOfAxiom> newaxioms=new HashSet<OWLSubClassOfAxiom>(); 
//	ArrayList<OWLClassExpression> templeft= new java.util.ArrayList<OWLClassExpression>();
//	ArrayList<OWLClassExpression> tempright= new java.util.ArrayList<OWLClassExpression>();
//	ArrayList<OWLClassExpression> templeft2= new java.util.ArrayList<OWLClassExpression>();
//	ArrayList<OWLClassExpression> tempright2= new java.util.ArrayList<OWLClassExpression>();
////	java.util.Collection<OWLAnnotation> annotation=new HashSet<OWLAnnotation>(); 
//    
//            
//	        //exists R.A on the l.h.s.	
//			if (c.get(0).getClassExpressionType().equals(ClassExpressionType.OBJECT_SOME_VALUES_FROM)){
//			OWLObjectSomeValuesFrom exists = (OWLObjectSomeValuesFrom) c.get(0);
//			OWLObjectPropertyExpression role = exists.getProperty();
//			OWLClassExpression filler = exists.getFiller();
//				
//			//inv(R) is generating
//			if (generatingRoles.contains(role.getInverseProperty().getSimplified())) {
//				
//				//the case: exists R.A \sqcap \top \sqs B or \bottom, 
//				if (c.size()==2 && d.size()==1 && c.get(1).isOWLThing()&&(d.get(0).getClassExpressionType().equals(ClassExpressionType.OWL_CLASS)||d.get(0).isOWLNothing())){
//					templeft.add(filler);
//					tempright.add(new OWLObjectAllValuesFromImpl(exists.getProperty().getInverseProperty().getSimplified(), d.get(0)));
//					//adding A \sqcap \forall inv(R).B/ \bottom
//					addAndRewriteGCI(newaxioms, templeft, tempright, nonRW);
//				//	newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (templeft, tempright));
//					//further on, if R is generating, add the original axiom
//				    if (generatingRoles.contains(role)) //newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (c, d));
//				    	addAndRewriteGCI(newaxioms, c, d, nonRW);
//				} else if (c.size()==2 && d.size()==1 && c.get(1).getClassExpressionType().equals(ClassExpressionType.OWL_CLASS)&&d.get(0).isOWLNothing()){
//					//the case: exists R.A \sqcap B \sqs \bottom,
//					templeft.add(filler);
//					templeft.add(new OWLObjectSomeValuesFromImpl(exists.getProperty().getInverseProperty().getSimplified(), c.get(1)));
//					//adding A \sqcap \forall inv(R).B/ \bottom
//				//	newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (templeft, d));
//					addAndRewriteGCI(newaxioms, templeft, d, nonRW);
//
//					//further on, if R is generating, add the original axiom
//				    if (generatingRoles.contains(role)) //newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (c, d));
//				    	addAndRewriteGCI(newaxioms, c, d, nonRW);
//
//				}
//				else
//				{
//					// \exists R.A has to be isolated:
//				//replacing existential with a new class name x which is placed at the end of the list
//				OWLClass x = OWLManager.getOWLDataFactory().getOWLClass(IRI.create("internal:def#rew" + freshClassCounter++));
//				c.remove(0);
//				c.add(x);
////				newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (c, d));
//				newaxioms.addAll(GCIrewrite(c,d, generatingRoles, nonRW));
//
////				addAndRewriteGCI(newaxioms, c, d, nonRW);
//			
//				//adding A \sqcap \forall inv(R).X
//				templeft.add(filler);
//				tempright.add(new OWLObjectAllValuesFromImpl(exists.getProperty().getInverseProperty().getSimplified(), x));
//				//newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (templeft, tempright));
//				addAndRewriteGCI(newaxioms, templeft, tempright, nonRW);
//				
//				//newaxioms.add(m_factory.getOWLSubClassOfAxiom(m_factory.getOWLObjectIntersectionOf(new HashSet<OWLClassExpression>(templeft)), m_factory.getOWLObjectUnionOf(new HashSet<OWLClassExpression>(tempright))));	
//               
//				//further on, if R is generating, add exists R.A \sqcap x 
//				templeft2.add(exists);
//				tempright2.add(x);
//			    if (generatingRoles.contains(role)) //newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (templeft2, tempright2));
//			    	addAndRewriteGCI(newaxioms, templeft2, tempright2, nonRW);
//
//			    }
//			}
//			else{//when the inverse role is not generating move the existential at the end of the list and go on processing - if there is anything to be processed
//				if (c.get(1).getClassExpressionType().equals(ClassExpressionType.OBJECT_SOME_VALUES_FROM)||d.get(0).getClassExpressionType().equals(ClassExpressionType.OBJECT_ALL_VALUES_FROM))
//				{
//				c.remove(0);
//				c.add(exists);
//				//the new axiom will have to be processed as well
//				newaxioms.addAll(GCIrewrite(c,d, generatingRoles, nonRW));
//			}
//				else addAndRewriteGCI(newaxioms, c, d, nonRW);
//			}
//			}
//			else //no l.h.s. existential needs to be processed
//				if (d.get(0).getClassExpressionType().equals(ClassExpressionType.OBJECT_ALL_VALUES_FROM)){
//				
//					OWLObjectAllValuesFrom forall = (OWLObjectAllValuesFrom) d.get(0);
//					OWLObjectPropertyExpression role = forall.getProperty();
//					OWLClassExpression filler = forall.getFiller();
//						
//					//inv(R) is generating or R is not generating
//					if (generatingRoles.contains(role.getInverseProperty().getSimplified())||!generatingRoles.contains(role)) {
//						//the case: A  or \top \sqcap forall R B \sqcup \bottom, 
//						if (c.size()==1 && d.size()==2 && d.get(1).isOWLNothing()&&(c.get(0).getClassExpressionType().equals(ClassExpressionType.OWL_CLASS)||c.get(0).isOWLThing())){
//							templeft.add(new OWLObjectSomeValuesFromImpl(forall.getProperty().getInverseProperty().getSimplified(), c.get(0)));
//							tempright.add(filler);
//							//adding   \forall inv(R).A/\top \sqcap B/
//							//newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (templeft, tempright));
//							addAndRewriteGCI(newaxioms, templeft, tempright, nonRW);
//							//further on, if R is generating, add the original axiom
//						    if (generatingRoles.contains(role)) //newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (c, d));
//						    	addAndRewriteGCI(newaxioms, c, d, nonRW);
//						} else if (d.size()==2 && c.size()==1 && d.get(1).getClassExpressionType().equals(ClassExpressionType.OWL_CLASS)&&c.get(0).isOWLThing()){
//							//the case: \top \sqs \forall R.B \sqcup A,
//							tempright.add(filler);
//							tempright.add(new OWLObjectAllValuesFromImpl(forall.getProperty().getInverseProperty().getSimplified(), d.get(1)));
//							//adding \top \sqs B \sqcup \forall inv(R).A
//							//newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (c, tempright));
//							addAndRewriteGCI(newaxioms, c, tempright, nonRW);
//
//							//further on, if R is generating, add the original axiom
//						    if (generatingRoles.contains(role)) //newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (c, d));
//						    	addAndRewriteGCI(newaxioms, c, d, nonRW);
//								//newaxioms.add(m_factory.getOWLSubClassOfAxiom(m_factory.getOWLObjectIntersectionOf(new HashSet(c)), m_factory.getOWLObjectUnionOf(new HashSet(d))));
//
//						}
//						else
//						{
//							// \forall R.A has to be isolated:
//						//replacing universal with a new class name x which is placed at the end of the disjuction list
//						OWLClass x = OWLManager.getOWLDataFactory().getOWLClass(IRI.create("internal:def#rew" + freshClassCounter++));
//						d.remove(0);
//						d.add(x);
//						//the new axiom will have to be processed as well
//						newaxioms.addAll(GCIrewrite(c,d, generatingRoles, nonRW));
//						
//						//adding   \exists inv(R).X \sqs A
//						tempright.add(filler);
//						templeft.add(new OWLObjectSomeValuesFromImpl(forall.getProperty().getInverseProperty().getSimplified(), x));
//					//	newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (templeft, tempright));
//						addAndRewriteGCI(newaxioms, templeft, tempright, nonRW);
//
//		               
//						//further on, if R is generating, add X \sqs \forall R.A 
//						tempright2.add(forall);
//						templeft2.add(x);
//					    if (generatingRoles.contains(role)) //newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (templeft2, tempright2));
//					    	addAndRewriteGCI(newaxioms, templeft2, tempright2, nonRW);
//
//					    }
//					}
//					else{//when the inverse role is not generating move the universal at the end of the list and go on processing
//						
//						if (d.get(1).getClassExpressionType().equals(ClassExpressionType.OBJECT_ALL_VALUES_FROM))
//						{
//							d.remove(0);
//							d.add(forall);
//							newaxioms=GCIrewrite(c,d, generatingRoles, nonRW);
//					}
//						else addAndRewriteGCI(newaxioms, c, d, nonRW);
//					}
//			
//				}
//				else //nothing needs to be processed
//			//		newaxioms.add(new java.util.AbstractMap.SimpleEntry<> (c, d));
//					addAndRewriteGCI(newaxioms, c, d, nonRW);
//          return newaxioms;
//	}		
	
}
