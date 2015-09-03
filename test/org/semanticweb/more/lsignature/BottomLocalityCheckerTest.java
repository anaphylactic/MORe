package org.semanticweb.more.lsignature;
import static org.junit.Assert.assertTrue;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.more.reasoner.LocalityInfo;
import org.semanticweb.more.util.Utility;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.PrefixManager;
import org.semanticweb.owlapi.util.DefaultPrefixManager;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;


public class BottomLocalityCheckerTest{

	
	static OWLClass a;
	static OWLClass b;
	static OWLClass c;
	static OWLClass d;
	static OWLClass e;
	static OWLClass f;
	static OWLObjectProperty r;
	static OWLObjectProperty s;
	static OWLDataProperty t;
	static OWLDataProperty u;
	static OWLIndividual i;
	static OWLIndividual j;
	static OWLDataFactory factory;
	static BottomLocalityChecker tester;

	static Set<OWLEntity> signature;
	static OWLAxiom axiom;
	static LocalityInfo locInfo;
	static List<Set<OWLEntity>> expectedSolutions;
	static OWLClassExpression auxClassExp1;
	static OWLClassExpression auxClassExp2;
	static OWLClassExpression auxClassExp3;
	static OWLClassExpression auxClassExp4;
	static Set<OWLEntity> auxSet;
	static Set<OWLIndividual> auxSetIndiv;
	static Set<OWLClassExpression> auxSetClassExp;
	static LinkedList<OWLObjectPropertyExpression> auxList;
	
	@BeforeClass
	public static void setUp(){
		tester = new BottomLocalityChecker();
		factory = new OWLDataFactoryImpl();
		PrefixManager prefManager = new DefaultPrefixManager();
		
		a = factory.getOWLClass("A",prefManager);
		b = factory.getOWLClass("B",prefManager);
		c = factory.getOWLClass("C",prefManager);
		d = factory.getOWLClass("D",prefManager);
		e = factory.getOWLClass("E",prefManager);
		f = factory.getOWLClass("F",prefManager);
		r = factory.getOWLObjectProperty("R", prefManager);
		s = factory.getOWLObjectProperty("S", prefManager);
		t = factory.getOWLDataProperty("T", prefManager);
		u = factory.getOWLDataProperty("U", prefManager);
		i = factory.getOWLNamedIndividual("I", prefManager);
		j = factory.getOWLNamedIndividual("J", prefManager);
	}
	
	
	
	@Test
	public void testIsLocalAxiom() {
		//////////////////////
		//OWLSubClassOfAxiom//
		//////////////////////
		
		//(A and B) sby (forall R.C)
		auxClassExp1 = factory.getOWLObjectIntersectionOf(a,b);
		auxClassExp2 = factory.getOWLObjectAllValuesFrom(r,c);
		axiom = factory.getOWLSubClassOfAxiom(auxClassExp1,auxClassExp2);
		
		signature = new HashSet<OWLEntity>();
		signature.add(a);
		signature.add(b);
		signature.add(c);
		signature.add(r);
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		
		/////////////////////////////////
		//OWLDisjointClassesAxiom axiom//
		/////////////////////////////////
		
		//Disjoint(A,B,C,D)
		axiom = factory.getOWLDisjointClassesAxiom(a,b,c,d);		
		signature = new HashSet<OWLEntity>();
		signature.add(a);
		signature.add(b);
		signature.add(c);
		signature.add(d);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(d);
		auxSet.add(c);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		auxSet.add(d);
		auxSet.add(c);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(a);
		auxSet.add(d);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(a);
		auxSet.add(c);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));

		
		
		///////////////////////////////////
		//OWLEquivalentClassesAxiom axiom//
		///////////////////////////////////
		
		//Equivalent(A and B,C,D)
		auxClassExp1 = factory.getOWLObjectIntersectionOf(a,b);
		axiom = factory.getOWLEquivalentClassesAxiom(auxClassExp1,c,d);		
		signature = new HashSet<OWLEntity>();
		signature.add(a);
		signature.add(b);
		signature.add(c);
		signature.add(d);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(c);
		auxSet.add(d);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		auxSet.add(c);
		auxSet.add(d);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));

		
		
		///////////////////////////////
		//OWLDisjointUnionAxiom axiom//
		///////////////////////////////
		
		//A = DisjUnion(B,C,D and E)
		auxClassExp1 = factory.getOWLObjectIntersectionOf(d,e);
		auxSetClassExp = new HashSet<OWLClassExpression>();
		auxSetClassExp.add(b);
		auxSetClassExp.add(c);
		auxSetClassExp.add(auxClassExp1);
		axiom = factory.getOWLDisjointUnionAxiom(a, auxSetClassExp);		
		signature = new HashSet<OWLEntity>();
		signature.add(b);
		signature.add(c);
		signature.add(d);
		signature.add(e);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(c);
		auxSet.add(d);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(c);
		auxSet.add(e);
		expectedSolutions.add(auxSet);
		
		//System.out.println(locInfo.getSolutions());
		//System.out.println(expectedSolutions.toString());
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));

		
		
		/////////////////////////////////////
		//OWLSubObjectPropertyOfAxiom axiom//
		/////////////////////////////////////
		
		//SubProperty(R,S)
		axiom = factory.getOWLSubObjectPropertyOfAxiom(r,s);		
		signature = new HashSet<OWLEntity>();
		signature.add(r);
		signature.add(s);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));		
		
		
		
		///////////////////////////////////
		//OWLSubDataPropertyOfAxiom axiom//
		///////////////////////////////////
		
		//SubProperty(T,U)
		axiom = factory.getOWLSubDataPropertyOfAxiom(t,u);
		
		signature = new HashSet<OWLEntity>();
		signature.add(t);
		signature.add(u);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(t);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));		
		
		
		
		////////////////////////////////////////////
		//OWLEquivalentObjectPropertiesAxiom axiom//
		////////////////////////////////////////////
		
		//Equiv(inv(R),S)
		axiom = factory.getOWLEquivalentObjectPropertiesAxiom(factory.getOWLObjectInverseOf(r),s);
		
		signature = new HashSet<OWLEntity>();
		signature.add(r);
		signature.add(s);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		auxSet.add(s);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));		
		
		
		
		//////////////////////////////////////////
		//OWLEquivalentDataPropertiesAxiom axiom//
		//////////////////////////////////////////
		
		//Equiv(T,U)
		axiom = factory.getOWLEquivalentDataPropertiesAxiom(t,u);
		
		signature = new HashSet<OWLEntity>();
		signature.add(t);
		signature.add(u);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(t);
		auxSet.add(u);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));		


		
		//////////////////////////////////////////
		//OWLDisjointObjectPropertiesAxiom axiom//
		//////////////////////////////////////////
		
		//Disj(inv(R),S)
		axiom = factory.getOWLDisjointObjectPropertiesAxiom(factory.getOWLObjectInverseOf(r),s);
		
		signature = new HashSet<OWLEntity>();
		signature.add(r);
		signature.add(s);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(s);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));		
		
		
		
		////////////////////////////////////////
		//OWLDisjointDataPropertiesAxiom axiom//
		////////////////////////////////////////
		
		//Disj(T,U)
		axiom = factory.getOWLDisjointDataPropertiesAxiom(t,u);
		
		signature = new HashSet<OWLEntity>();
		signature.add(t);
		signature.add(u);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(t);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(u);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		
		//////////////////////////////////////////
		//OWLFunctionalObjectPropertyAxiom axiom//
		//////////////////////////////////////////
		
		//Func(R)
		axiom = factory.getOWLFunctionalObjectPropertyAxiom(r);
		
		signature = new HashSet<OWLEntity>();
		signature.add(r);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));		
		
		
		
		////////////////////////////////////////
		//OWLFunctionalDataPropertyAxiom axiom//
		////////////////////////////////////////
		
		//Func(T)
		axiom = factory.getOWLFunctionalDataPropertyAxiom(t);
		
		signature = new HashSet<OWLEntity>();
		signature.add(t);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(t);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		
		/////////////////////////////////////////////////
		//OWLInverseFunctionalObjectPropertyAxiom axiom//
		/////////////////////////////////////////////////
		
		//InvFunc(R)
		axiom = factory.getOWLInverseFunctionalObjectPropertyAxiom(r);
		
		signature = new HashSet<OWLEntity>();
		signature.add(r);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));		
		

		
		/////////////////////////////////////////
		//OWLInverseObjectPropertiesAxiom axiom//
		/////////////////////////////////////////
		
		//Inverse(R,S)
		axiom = factory.getOWLInverseObjectPropertiesAxiom(r,s);
		
		signature = new HashSet<OWLEntity>();
		signature.add(r);
		signature.add(s);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		auxSet.add(s);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));		

		
		
		///////////////////////////////////////////
		//OWLIrreflexiveObjectPropertyAxiom axiom//
		///////////////////////////////////////////
		
		//Irref(R)
		axiom = factory.getOWLIrreflexiveObjectPropertyAxiom(r);
		
		signature = new HashSet<OWLEntity>();
		signature.add(r);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));		

		
		
		//////////////////////////////////////////
		//OWLAsymmetricObjectPropertyAxiom axiom//
		//////////////////////////////////////////
		
		//Asym(R)
		axiom = factory.getOWLAsymmetricObjectPropertyAxiom(r);
		
		signature = new HashSet<OWLEntity>();
		signature.add(r);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));		
		
		
		
		/////////////////////////////////////////
		//OWLReflexiveObjectPropertyAxiom axiom//
		/////////////////////////////////////////
		
		//Reflexive(R)
		axiom = factory.getOWLReflexiveObjectPropertyAxiom(r);
		
		signature = new HashSet<OWLEntity>();
		signature.add(r);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));		
		
		
		
		/////////////////////////////////////////
		//OWLSymmetricObjectPropertyAxiom axiom//
		/////////////////////////////////////////
		
		//Symm(R)
		axiom = factory.getOWLSymmetricObjectPropertyAxiom(r);
		
		signature = new HashSet<OWLEntity>();
		signature.add(r);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));		
				
		
		
		//////////////////////////////////////////
		//OWLTransitiveObjectPropertyAxiom axiom//
		//////////////////////////////////////////
		
		//Trans(R)
		axiom = factory.getOWLTransitiveObjectPropertyAxiom(r);
		
		signature = new HashSet<OWLEntity>();
		signature.add(r);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));		

		
		
		//////////////////////////////////////
		//OWLObjectPropertyDomainAxiom axiom//
		//////////////////////////////////////
		
		//ObjectPropDomain(R,not(A))
		axiom = factory.getOWLObjectPropertyDomainAxiom(r, factory.getOWLObjectComplementOf(a));
		
		signature = new HashSet<OWLEntity>();
		signature.add(r);
		signature.add(a);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));		


		
		////////////////////////////////////
		//OWLDataPropertyDomainAxiom axiom//
		////////////////////////////////////
		
		//DataPropDomain(T,not(A))
		axiom = factory.getOWLDataPropertyDomainAxiom(t, factory.getOWLObjectComplementOf(a));
		
		signature = new HashSet<OWLEntity>();
		signature.add(t);
		signature.add(a);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(t);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));		


		
		//////////////////////////////////////
		//OWLObjectPropertyRangeAxiom axiom//
		//////////////////////////////////////
		
		//ObjPropRange(R,not(A))
		axiom = factory.getOWLObjectPropertyRangeAxiom(r, factory.getOWLObjectComplementOf(a));
		
		signature = new HashSet<OWLEntity>();
		signature.add(r);
		signature.add(a);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));		

		

		//////////////////////////////////////
		//OWLDataPropertyRangeAxiom axiom//
		//////////////////////////////////////
		
		//DataPropRange(T,integer)
		axiom = factory.getOWLDataPropertyRangeAxiom(t, factory.getIntegerOWLDatatype());
		
		signature = new HashSet<OWLEntity>();
		signature.add(t);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(t);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		
		////////////////////////////////////
		//OWLSubPropertyChainOfAxiom axiom//
		////////////////////////////////////
		
		//SubPropChain(RSRS,R)
		auxList = new LinkedList<OWLObjectPropertyExpression>();
		auxList.add(r);
		auxList.add(s);
		auxList.add(r);
		auxList.add(s);
		axiom = factory.getOWLSubPropertyChainOfAxiom(auxList,r);
		
		signature = new HashSet<OWLEntity>();
		signature.add(r);
		signature.add(s);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(s);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));		

		
		/////////////////////////////
		//OWLDeclarationAxiom axiom//
		/////////////////////////////
		
		//Class(A)
		axiom = factory.getOWLDeclarationAxiom(a);
		
		signature = new HashSet<OWLEntity>();
		signature.add(a);
		
		locInfo = tester.isLocalAxiom(axiom, signature, new HashSet<OWLEntity>());
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));	
	}
	

	
	@Test
	public void testIsBottomClass() {
		////////////////
		//OWLClass exp//
		////////////////
		
		// A
		OWLClassExpression exp = a;
		
		signature = new HashSet<OWLEntity>();
		signature.add(a);
		tester.externalSignature = signature;
		tester.globalEntities = new HashSet<OWLEntity>();
		
		locInfo = tester.isBottomClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		
		///////////////////////////////
		//OWLObjectIntersectionOf exp//
		///////////////////////////////
		
		// A and B and C
		exp = factory.getOWLObjectIntersectionOf(a,b,c);
		
		signature = new HashSet<OWLEntity>();
		signature.add(a);
		signature.add(b);
		signature.add(c);
		tester.externalSignature = signature;
		
		locInfo = tester.isBottomClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(c);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		

		
		////////////////////////
		//OWLObjectUnionOf exp//
		////////////////////////
		
		// (A and B) or (C and D)
		exp = factory.getOWLObjectUnionOf(factory.getOWLObjectIntersectionOf(a,b),factory.getOWLObjectIntersectionOf(c,d));
		
		signature = new HashSet<OWLEntity>();
		signature.add(a);
		signature.add(b);
		signature.add(c);
		signature.add(d);
		tester.externalSignature = signature;
		
		locInfo = tester.isBottomClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		auxSet.add(c);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		auxSet.add(d);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(c);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(d);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		
		/////////////////////////////
		//OWLObjectComplementOf exp//
		/////////////////////////////
		
		// not(A or not(B))
		exp = factory.getOWLObjectComplementOf(factory.getOWLObjectUnionOf(a,factory.getOWLObjectComplementOf(b)));
		
		signature = new HashSet<OWLEntity>();
		signature.add(a);
		signature.add(b);
		tester.externalSignature = signature;
		
		locInfo = tester.isBottomClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		
		//////////////////////////////
		//OWLObjectOneOf         exp//
		//OWLDataOneOf           exp//
		//OWLObjectAllValuesFrom exp//
		//OWLDataAllValuesFrom   exp//
		//////////////////////////////
		//NO TEST
		
		
		
		///////////////////////////////
		//OWLObjectSomeValuesFrom exp//
		///////////////////////////////
		
		// some(R,A)
		exp = factory.getOWLObjectSomeValuesFrom(r,a);
		
		signature = new HashSet<OWLEntity>();
		signature.add(a);
		signature.add(r);
		tester.externalSignature = signature;
		
		locInfo = tester.isBottomClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		
		/////////////////////////////
		//OWLDataSomeValuesFrom exp//
		/////////////////////////////
		
		// some(t,integer)
		exp = factory.getOWLDataSomeValuesFrom(t,factory.getIntegerOWLDatatype());
		
		signature = new HashSet<OWLEntity>();
		signature.add(t);
		tester.externalSignature = signature;
		
		locInfo = tester.isBottomClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(t);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		
		////////////////////////
		//OWLObjectHasSelf exp//
		////////////////////////
		
		// hasSelf(r)
		exp = factory.getOWLObjectHasSelf(r);
		
		signature = new HashSet<OWLEntity>();
		signature.add(r);
		tester.externalSignature = signature;
		
		locInfo = tester.isBottomClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		
		////////////////////////
		//OWLObjectHasValue exp//
		////////////////////////
		
		// ObjectHasValue(r,i)
		exp = factory.getOWLObjectHasValue(r, i);
		
		signature = new HashSet<OWLEntity>();
		signature.add(r);
		tester.externalSignature = signature;
		
		locInfo = tester.isBottomClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		
		////////////////////////
		//OWLDataHasValue exp//
		////////////////////////
		
		// DataHasValue(t,1)
		exp = factory.getOWLDataHasValue(t, factory.getOWLLiteral(1));
		
		signature = new HashSet<OWLEntity>();
		signature.add(t);
		tester.externalSignature = signature;
		
		locInfo = tester.isBottomClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(t);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		
		///////////////////////////////
		//OWLObjectMinCardinality exp//
		///////////////////////////////
		
		// ObjectMinCard(3,R,A)
		exp = factory.getOWLObjectMinCardinality(3,r,a);
		
		signature = new HashSet<OWLEntity>();
		signature.add(r);
		signature.add(a);
		tester.externalSignature = signature;
		
		locInfo = tester.isBottomClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		
		///////////////////////////////
		//OWLDataMinCardinality exp//
		///////////////////////////////
		
		// DataMinCard(3,t)
		exp = factory.getOWLDataMinCardinality(3,t);
		
		signature = new HashSet<OWLEntity>();
		signature.add(t);
		tester.externalSignature = signature;
		
		locInfo = tester.isBottomClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(t);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		
		///////////////////////////////
		//OWLObjectMaxCardinality exp//
		//OWLDataMaxCardinality   exp//
		///////////////////////////////
		//NO TEST
		
		
		
		///////////////////////////////
		//OWLObjectExactCardinality exp//
		///////////////////////////////
		
		// ObjectExactCard(3,R,A)
		exp = factory.getOWLObjectExactCardinality(3,r,a);
		
		signature = new HashSet<OWLEntity>();
		signature.add(r);
		signature.add(a);
		tester.externalSignature = signature;
		
		locInfo = tester.isBottomClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		
		///////////////////////////////
		//OWLDataExactCardinality exp//
		///////////////////////////////
		
		// DataExactCard(3,t)
		exp = factory.getOWLDataExactCardinality(3,t);
		
		signature = new HashSet<OWLEntity>();
		signature.add(t);
		tester.externalSignature = signature;
		
		locInfo = tester.isBottomClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(t);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
	}
	
	
	
	@Test
	public void testIsTopClass() {
		////////////////
		//OWLClass exp//
		////////////////
		
		// A
		OWLClassExpression exp = a;
		
		signature = new HashSet<OWLEntity>();
		signature.add(a);
		tester.externalSignature = signature;
		tester.globalEntities = new HashSet<OWLEntity>();
		
		locInfo = tester.isBottomClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		
		///////////////////////////////
		//OWLObjectIntersectionOf exp//
		///////////////////////////////
	
		// (not(A) or not(B)) and (not(C) or not(D))
		exp = factory.getOWLObjectIntersectionOf(factory.getOWLObjectUnionOf(factory.getOWLObjectComplementOf(a),factory.getOWLObjectComplementOf(b)),factory.getOWLObjectUnionOf(factory.getOWLObjectComplementOf(c),factory.getOWLObjectComplementOf(d)));
		
		signature = new HashSet<OWLEntity>();
		signature.add(a);
		signature.add(b);
		signature.add(c);
		signature.add(d);
		tester.externalSignature = signature;
		
		locInfo = tester.isTopClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		auxSet.add(c);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		auxSet.add(d);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(c);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(d);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		

		
		////////////////////////
		//OWLObjectUnionOf exp//
		////////////////////////
		
		// not(A) or (forall(R,not(B))
		exp = factory.getOWLObjectUnionOf(factory.getOWLObjectComplementOf(a),factory.getOWLObjectAllValuesFrom(r,factory.getOWLObjectComplementOf(b)));
		
		signature = new HashSet<OWLEntity>();
		signature.add(a);
		signature.add(b);
		signature.add(r);
		tester.externalSignature = signature;
		
		locInfo = tester.isTopClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		
		/////////////////////////////
		//OWLObjectComplementOf exp//
		/////////////////////////////
		
		// not(A and B)
		exp = factory.getOWLObjectComplementOf(factory.getOWLObjectIntersectionOf(a,b));
		
		signature = new HashSet<OWLEntity>();
		signature.add(a);
		signature.add(b);
		tester.externalSignature = signature;
		
		locInfo = tester.isTopClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		//////////////////////////////
		//OWLObjectOneOf         exp//
		//OWLDataOneOf           exp//
		//////////////////////////////
		//NO TEST		
		
		
		
		//////////////////////////////
		//OWLObjectAllValuesFrom exp//
		//////////////////////////////

		// all(R,not(A))
		exp = factory.getOWLObjectAllValuesFrom(r,factory.getOWLObjectComplementOf(a));
		
		signature = new HashSet<OWLEntity>();
		signature.add(a);
		signature.add(r);
		tester.externalSignature = signature;
		
		locInfo = tester.isTopClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		
		////////////////////////////
		//OWLDataAllValuesFrom exp//
		////////////////////////////
		
		// all(T,integer)
		exp = factory.getOWLDataAllValuesFrom(t,factory.getIntegerOWLDatatype());
		
		signature = new HashSet<OWLEntity>();
		signature.add(t);
		tester.externalSignature = signature;
		
		locInfo = tester.isTopClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(t);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		
		///////////////////////////////
		//OWLObjectSomeValuesFrom exp//
		//OWLDataSomeValuesFrom   exp//
		//OWLObjectHasSelf        exp//
		//OWLObjectHasValue       exp//
		//OWLDataHasValue         exp//
		//OWLObjectMinCardinality exp//
		//OWLDataMinCardinality   exp//
		///////////////////////////////
		//NO TEST		
		
		
		
		
		///////////////////////////////
		//OWLObjectMaxCardinality exp//
		///////////////////////////////
		
		// ObjMaxCard(3,R,A)
		exp = factory.getOWLObjectMaxCardinality(3, r, a);
		
		signature = new HashSet<OWLEntity>();
		signature.add(a);
		signature.add(r);
		tester.externalSignature = signature;
		
		locInfo = tester.isTopClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		expectedSolutions.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
		
		/////////////////////////////
		//OWLDataMaxCardinality exp//
		/////////////////////////////
		
		// DataMaxCard(3,T)
		exp = factory.getOWLDataMaxCardinality(3, t);
		
		signature = new HashSet<OWLEntity>();
		signature.add(t);
		tester.externalSignature = signature;
		
		locInfo = tester.isTopClass(exp);
		
		//isLocal
		assertTrue(!locInfo.is());
		//canMakeLocal
		assertTrue(locInfo.canMake());
		//solutions
		expectedSolutions = new LinkedList<Set<OWLEntity>>();
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(t);
		expectedSolutions.add(auxSet);
		
		assertTrue(Utility.compareCollections(new HashSet<Set<OWLEntity>>(expectedSolutions), new HashSet<Set<OWLEntity>>(locInfo.getSolutions())));
		
		
	}

}


