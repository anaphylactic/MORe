package org.semanticweb.more.structural;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;
import util.TestUtility;


public class OWLNormalization4MOReTest {

	static OWLClass a;
	static OWLClass b;
	static OWLClass c;
	static OWLClass d;
	static OWLClass e;
	static OWLClass f;
	static OWLClass g;
	OWLNamedIndividual i = factory.getOWLNamedIndividual(IRI.create("i"));
	OWLNamedIndividual j = factory.getOWLNamedIndividual(IRI.create("i"));
	static OWLObjectProperty p;
	static OWLObjectProperty q;
	static OWLObjectProperty r;
	static OWLObjectProperty s;
	static OWLObjectProperty t;
	static OWLObjectProperty u;
	static OWLDataFactoryImpl factory;

	
	@BeforeClass
	public static void createClasses(){
		factory = new OWLDataFactoryImpl();
		a = factory.getOWLClass(IRI.create("A"));
		b = factory.getOWLClass(IRI.create("B"));
		c = factory.getOWLClass(IRI.create("C"));
		d = factory.getOWLClass(IRI.create("D"));
		e = factory.getOWLClass(IRI.create("E"));
		f = factory.getOWLClass(IRI.create("F"));
		g = factory.getOWLClass(IRI.create("G"));
		p = factory.getOWLObjectProperty(IRI.create("P"));
		q = factory.getOWLObjectProperty(IRI.create("Q"));
		r = factory.getOWLObjectProperty(IRI.create("R"));
		s = factory.getOWLObjectProperty(IRI.create("S"));
		t = factory.getOWLObjectProperty(IRI.create("T"));
		u = factory.getOWLObjectProperty(IRI.create("U"));
		System.out.println("@BeforeClass executed");
	}
	
	
	@Test
	public void testDomainAxiom() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLObjectPropertyDomainAxiom(r, a);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> owl:Thing) <A>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		
	}
	
	@Test
	public void testRangeAxiom() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLObjectPropertyRangeAxiom(r, a);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(owl:Thing ObjectAllValuesFrom(<R> <A>))");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		
	}
	
	@Test
	public void testLhsExistentialPositiveFiller() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectIntersectionOf(
							a, 
							factory.getOWLObjectSomeValuesFrom(r, b)),
					factory.getOWLObjectIntersectionOf(
							c,
							d));
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<internal:def#0> <D>)");
			control.add("SubClassOf(ObjectIntersectionOf(<A> ObjectSomeValuesFrom(<R> <B>)) <internal:def#0>)");
			control.add("SubClassOf(<internal:def#0> <C>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		
	}
	
	@Test
	public void testLhsExistentialNegativeFiller() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectIntersectionOf(
							a, 
							factory.getOWLObjectSomeValuesFrom(r, factory.getOWLObjectComplementOf(b))),
					c);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<A> ObjectUnionOf(<C> ObjectAllValuesFrom(<R> <B>)))");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		
	}
	
	@Test
	public void testRhsExistentialPositiveFiller() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					a,
					factory.getOWLObjectUnionOf(
							factory.getOWLObjectSomeValuesFrom(r, b),
							c,
							d));
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<A> ObjectUnionOf(<C> <D> ObjectSomeValuesFrom(<R> <B>)))");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		
	}
	
	@Test
	public void testRhsExistentialNegativeFiller() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					a,
					factory.getOWLObjectUnionOf(
							factory.getOWLObjectSomeValuesFrom(r, factory.getOWLObjectComplementOf(b)),
							c,
							d));
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<A> ObjectUnionOf(<C> <D> ObjectSomeValuesFrom(<R> ObjectComplementOf(<B>))))");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		
	}
	
	@Test
	public void testPositiveNominalFillersLhs(){
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectSomeValuesFrom(r, factory.getOWLObjectOneOf(i)),
					a);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
		
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("ClassAssertion(<internal:def#0> <i>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <internal:def#0>) <A>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testNegativeNominalFillersLhs(){
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectSomeValuesFrom(s, factory.getOWLObjectComplementOf(factory.getOWLObjectOneOf(j))),
					b);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
		
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<internal:def#0> ObjectOneOf(<i>))");
			control.add("SubClassOf(owl:Thing ObjectUnionOf(<B> ObjectAllValuesFrom(<S> <internal:def#0>)))");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testPositiveNominalFillersRhs(){
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					a,
					factory.getOWLObjectSomeValuesFrom(r, factory.getOWLObjectOneOf(i)));
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
		
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<internal:def#0> ObjectOneOf(<i>))");
			control.add("SubClassOf(<A> ObjectSomeValuesFrom(<R> <internal:def#0>))");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testNegativeNominalFillersRhs(){
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLNamedIndividual i = factory.getOWLNamedIndividual(IRI.create("i"));
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					a,
					factory.getOWLObjectSomeValuesFrom(r, factory.getOWLObjectComplementOf(factory.getOWLObjectOneOf(i))));
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
		
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("ClassAssertion(ObjectComplementOf(<internal:def#0>) <i>)");
			control.add("SubClassOf(<A> ObjectSomeValuesFrom(<R> <internal:def#0>))");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testLhsUniversalPositiveFiller() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectIntersectionOf(
							a, 
							factory.getOWLObjectAllValuesFrom(r, b)),
					c);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<A> ObjectUnionOf(<C> ObjectSomeValuesFrom(<R> ObjectComplementOf(<B>))))");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		
	}
	
	@Test
	public void testLhsUniversalNegativeFiller() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectIntersectionOf(
							a, 
							factory.getOWLObjectAllValuesFrom(r, factory.getOWLObjectComplementOf(b))),
					c);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<A> ObjectUnionOf(<C> ObjectSomeValuesFrom(<R> <B>)))");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		
	}

	@Test
	public void testRhsUniversalPositiveFiller() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					a,
					factory.getOWLObjectUnionOf(
							factory.getOWLObjectAllValuesFrom(r, b),
							c));
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<A> ObjectUnionOf(<C> ObjectAllValuesFrom(<R> <B>)))");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		
	}
	
	@Test
	public void testRhsUniversalNegativeFiller() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					a,
					factory.getOWLObjectUnionOf(
							factory.getOWLObjectAllValuesFrom(r, factory.getOWLObjectComplementOf(b)),
							c));
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(ObjectIntersectionOf(<A> ObjectSomeValuesFrom(<R> <B>)) <C>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		
	}

	

	@Test
	public void testAssertionAxioms() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLClassAssertionAxiom(a,i);
			OWLAxiom ax2 = factory.getOWLObjectPropertyAssertionAxiom(r, i, j);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("ClassAssertion(<A> <i>)");
			control.add("ObjectPropertyAssertion(<R> <i> <i>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		
	}

	@Test
	public void testSimpleRoleInclusions() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubObjectPropertyOfAxiom(r, p);
			OWLAxiom ax2 = factory.getOWLSubObjectPropertyOfAxiom(q, s.getInverseProperty());
			OWLAxiom ax3 = factory.getOWLSubObjectPropertyOfAxiom(t.getInverseProperty(), u);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			axioms.add(ax3);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubObjectPropertyOf(<R> <P>)");
			control.add("SubObjectPropertyOf(<Q> InverseOf(<S>))");
			control.add("SubObjectPropertyOf(InverseOf(<T>) <U>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testComplexRoleInclusions() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			List<OWLObjectPropertyExpression> chain = new ArrayList<OWLObjectPropertyExpression>();
			chain.add(p);
			chain.add(q);
			OWLAxiom ax1 = factory.getOWLSubPropertyChainOfAxiom(chain,r);
			List<OWLObjectPropertyExpression> chain2 = new ArrayList<OWLObjectPropertyExpression>();
			chain2.add(s);
			chain2.add(t);
			OWLAxiom ax2 = factory.getOWLSubPropertyChainOfAxiom(chain2,s);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubObjectPropertyOf(ObjectPropertyChain( <S> <T> ) <S>)");
			control.add("SubObjectPropertyOf(ObjectPropertyChain( <P> <Q> ) <R>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testLhsHasSelf() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectHasSelf(r),
					a);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(ObjectHasSelf(<R>) <A>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testRhsHasSelf() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					a,
					factory.getOWLObjectHasSelf(r));
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<A> ObjectHasSelf(<R>))");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}

	
	@Test
	public void testFunctionality() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLFunctionalObjectPropertyAxiom(r);
			OWLAxiom ax2 = factory.getOWLInverseFunctionalObjectPropertyAxiom(s);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(owl:Thing ObjectMaxCardinality(1 <R> owl:Thing))");
			control.add("SubClassOf(owl:Thing ObjectMaxCardinality(1 InverseOf(<S>) owl:Thing))");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testRhsMinCardinality1() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					a,
					factory.getOWLObjectMinCardinality(0, r, b));
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Assert.assertTrue(normalization.getNormalizedOntology().isEmpty());
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testRhsMinCardinality2() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					c,
					factory.getOWLObjectMinCardinality(3, s, d));
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<C> <internal:def#MORe0>)");
			control.add("SubClassOf(<internal:def#MORe0> ObjectSomeValuesFrom(<S> <internal:def#MORe3>))");
			control.add("SubClassOf(<internal:def#MORe0> ObjectSomeValuesFrom(<S> <internal:def#MORe2>))");
			control.add("SubClassOf(<internal:def#MORe0> ObjectSomeValuesFrom(<S> <internal:def#MORe1>))");
			control.add("SubClassOf(ObjectIntersectionOf(<internal:def#MORe1> <internal:def#MORe2>) owl:Nothing)");
			control.add("SubClassOf(ObjectIntersectionOf(<internal:def#MORe1> <internal:def#MORe3>) owl:Nothing)");
			control.add("SubClassOf(ObjectIntersectionOf(<internal:def#MORe2> <internal:def#MORe3>) owl:Nothing)");
			control.add("SubClassOf(<internal:def#MORe3> <D>)");
			control.add("SubClassOf(<internal:def#MORe2> <D>)");
			control.add("SubClassOf(<internal:def#MORe1> <D>)");

			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	@Test
	public void testRhsMinCardinality3() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					e,
					factory.getOWLObjectMinCardinality(2, q));
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<internal:def#MORe0> ObjectSomeValuesFrom(<Q> <internal:def#MORe1>))");
			control.add("SubClassOf(<E> <internal:def#MORe0>)");
			control.add("SubClassOf(<internal:def#MORe0> ObjectSomeValuesFrom(<Q> <internal:def#MORe2>))");
			control.add("SubClassOf(ObjectIntersectionOf(<internal:def#MORe1> <internal:def#MORe2>) owl:Nothing)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testLhsMinCardinality1() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectMinCardinality(0, r, a),
					b);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(owl:Thing <B>)");

			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testLhsMinCardinality2() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectMinCardinality(3, s, c),
					d);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(owl:Thing ObjectUnionOf(<D> ObjectMaxCardinality(2 <S> <C>)))");

			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testLhsMinCardinality3() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectMinCardinality(2, q),
					a);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(owl:Thing ObjectUnionOf(<A> ObjectMaxCardinality(1 <Q> owl:Thing)))");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testRhsMaxCardinality1() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					a,
					factory.getOWLObjectMaxCardinality(0, r, b));
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);

			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(ObjectIntersectionOf(<A> ObjectSomeValuesFrom(<R> <B>)) owl:Nothing)");
			
			TestUtility.checkEqualSets(actual, control);			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testRhsMaxCardinality2() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					c,
					factory.getOWLObjectMaxCardinality(3, s, d));
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<C> ObjectMaxCardinality(3 <S> <D>))");

			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testRhsMaxCardinality3() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					e,
					factory.getOWLObjectMaxCardinality(2, q));
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<E> ObjectMaxCardinality(2 <Q> owl:Thing))");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testLhsMaxCardinality1() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectMaxCardinality(0, r, a),
					b);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(owl:Thing ObjectUnionOf(<B> ObjectSomeValuesFrom(<R> <A>)))");

			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testLhsMaxCardinality2() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectMaxCardinality(1, s, c),
					d);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<internal:def#MORe2> <C>)");
			control.add("SubClassOf(owl:Thing ObjectUnionOf(<D> <internal:def#MORe0>))");
			control.add("SubClassOf(<internal:def#MORe0> ObjectSomeValuesFrom(<S> <internal:def#MORe2>))");
			control.add("SubClassOf(<internal:def#MORe1> <C>)");
			control.add("SubClassOf(ObjectIntersectionOf(<internal:def#MORe1> <internal:def#MORe2>) owl:Nothing)");
			control.add("SubClassOf(<internal:def#MORe0> ObjectSomeValuesFrom(<S> <internal:def#MORe1>))");


			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testLhsMaxCardinality3() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectMaxCardinality(1, q),
					a);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o,false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<internal:def#MORe0> ObjectSomeValuesFrom(<Q> <internal:def#MORe1>))");
			control.add("SubClassOf(owl:Thing ObjectUnionOf(<A> <internal:def#MORe0>))");
			control.add("SubClassOf(<internal:def#MORe0> ObjectSomeValuesFrom(<Q> <internal:def#MORe2>))");
			control.add("SubClassOf(ObjectIntersectionOf(<internal:def#MORe1> <internal:def#MORe2>) owl:Nothing)");

			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testTransitivityNoEncoding() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					a,
					factory.getOWLObjectAllValuesFrom(r, b));
			OWLAxiom ax2 = factory.getOWLTransitiveObjectPropertyAxiom(r);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<A> ObjectAllValuesFrom(<R> <B>))");
			control.add("TransitiveObjectProperty(<R>)");

			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testTransitivityEncoding1() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					a,
					factory.getOWLObjectAllValuesFrom(r, b));
			OWLAxiom ax2 = factory.getOWLTransitiveObjectPropertyAxiom(r);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, true, true);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<A> ObjectAllValuesFrom(<R> <B>))");
			control.add("SubClassOf(<A> ObjectAllValuesFrom(<R> <internal:def#transEncoding0>))");
			control.add("SubClassOf(<internal:def#transEncoding0> ObjectAllValuesFrom(<R> <internal:def#transEncoding0>))");
			control.add("SubClassOf(<internal:def#transEncoding0> <B>)");
						
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testTransitivityEncoding2() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					a,
					factory.getOWLObjectAllValuesFrom(r, b));
			OWLAxiom ax2 = factory.getOWLTransitiveObjectPropertyAxiom(s);
			OWLAxiom ax3 = factory.getOWLSubObjectPropertyOfAxiom(s, r);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			axioms.add(ax3);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, true, true);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubObjectPropertyOf(<S> <R>)");
			control.add("SubClassOf(<A> ObjectAllValuesFrom(<R> <B>))");
			control.add("SubClassOf(<A> ObjectAllValuesFrom(<S> <internal:def#transEncoding0>))");
			control.add("SubClassOf(<internal:def#transEncoding0> ObjectAllValuesFrom(<S> <internal:def#transEncoding0>))");
			control.add("SubClassOf(<internal:def#transEncoding0> <B>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	
	@Test
	public void testTransitivityEncoding3() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectSomeValuesFrom(r, a),
					b);
			OWLAxiom ax2 = factory.getOWLTransitiveObjectPropertyAxiom(r);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, true, true);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <A>) <B>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <A>) <internal:def#transEncoding0>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <internal:def#transEncoding0>) <internal:def#transEncoding0>)");
			control.add("SubClassOf(<internal:def#transEncoding0> <B>)");

			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testTransitivityEncoding4() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectSomeValuesFrom(r, a),
					b);
			OWLAxiom ax2 = factory.getOWLTransitiveObjectPropertyAxiom(s);
			OWLAxiom ax3 = factory.getOWLSubObjectPropertyOfAxiom(s, r);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			axioms.add(ax3);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, true, true);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubObjectPropertyOf(<S> <R>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <A>) <B>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<S> <A>) <internal:def#transEncoding0>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<S> <internal:def#transEncoding0>) <internal:def#transEncoding0>)");
			control.add("SubClassOf(<internal:def#transEncoding0> <B>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testTransitivityEncoding5() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectSomeValuesFrom(r, a),
					factory.getOWLObjectComplementOf(b));
			OWLAxiom ax2 = factory.getOWLTransitiveObjectPropertyAxiom(r);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, true, true);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(ObjectIntersectionOf(<B> ObjectSomeValuesFrom(<R> <A>)) owl:Nothing)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <A>) <internal:def#transEncoding0>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <internal:def#transEncoding0>) <internal:def#transEncoding0>)");
			control.add("SubClassOf(ObjectIntersectionOf(<B> <internal:def#transEncoding0>) owl:Nothing)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testTransitivityEncoding6() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectIntersectionOf(
							factory.getOWLObjectSomeValuesFrom(r, a),
							b),
					c);
			OWLAxiom ax2 = factory.getOWLTransitiveObjectPropertyAxiom(r);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, true, true);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(ObjectIntersectionOf(<B> <internal:def#transEncoding0>) <C>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <A>) <internal:def#transEncoding0>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <A>) <internal:def#transEncoding1>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <internal:def#transEncoding1>) <internal:def#transEncoding1>)");
			control.add("SubClassOf(<internal:def#transEncoding1> <internal:def#transEncoding0>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testTransitivityEncoding7() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					a,
					factory.getOWLObjectUnionOf(
							factory.getOWLObjectAllValuesFrom(r, b), 
							c));
			OWLAxiom ax2 = factory.getOWLTransitiveObjectPropertyAxiom(r);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, true, true);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<A> ObjectUnionOf(<C> <internal:def#transEncoding0>))");
			control.add("SubClassOf(<internal:def#transEncoding0> ObjectAllValuesFrom(<R> <B>))");
			control.add("SubClassOf(<internal:def#transEncoding0> ObjectAllValuesFrom(<R> <internal:def#transEncoding1>))");
			control.add("SubClassOf(<internal:def#transEncoding1> ObjectAllValuesFrom(<R> <internal:def#transEncoding1>))");
			control.add("SubClassOf(<internal:def#transEncoding1> <B>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		
		}
	}
	
	@Test
	public void testTransitivityEncoding8() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLThing(),
					factory.getOWLObjectUnionOf(
							factory.getOWLObjectAllValuesFrom(r, b), 
							a));
			OWLAxiom ax2 = factory.getOWLTransitiveObjectPropertyAxiom(r);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, true, true);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(owl:Thing ObjectUnionOf(<A> ObjectAllValuesFrom(<R> <B>)))");
			control.add("SubClassOf(owl:Thing ObjectUnionOf(<A> ObjectAllValuesFrom(<R> <internal:def#transEncoding0>)))");
			control.add("SubClassOf(<internal:def#transEncoding0> ObjectAllValuesFrom(<R> <internal:def#transEncoding0>))");
			control.add("SubClassOf(<internal:def#transEncoding0> <B>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		
		}
	}
	
	@Test
	public void testTransitivityEncoding9() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLThing(),
					factory.getOWLObjectUnionOf(
							factory.getOWLObjectAllValuesFrom(r, b), 
							factory.getOWLObjectAllValuesFrom(s,a)));
			OWLAxiom ax2 = factory.getOWLTransitiveObjectPropertyAxiom(r);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, true, true);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(owl:Thing ObjectUnionOf(<internal:def#transEncoding0> ObjectAllValuesFrom(<S> <A>)))");
			control.add("SubClassOf(<internal:def#transEncoding0> ObjectAllValuesFrom(<R> <B>))");
			control.add("SubClassOf(<internal:def#transEncoding0> ObjectAllValuesFrom(<R> <internal:def#transEncoding1>))");
			control.add("SubClassOf(<internal:def#transEncoding1> ObjectAllValuesFrom(<R> <internal:def#transEncoding1>))");
			control.add("SubClassOf(<internal:def#transEncoding1> <B>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		
		}
	}
	
	@Test
	public void testTransitivityEncoding10() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectSomeValuesFrom(r, a),
					factory.getOWLObjectComplementOf(b));
			OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectSomeValuesFrom(r, c),
					b);
			OWLAxiom ax3 = factory.getOWLTransitiveObjectPropertyAxiom(r);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			axioms.add(ax3);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, true, true);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(ObjectIntersectionOf(<B> ObjectSomeValuesFrom(<R> <A>)) owl:Nothing)");
			control.add("SubClassOf(ObjectIntersectionOf(<B> <internal:def#transEncoding0>) owl:Nothing)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <internal:def#transEncoding0>) <internal:def#transEncoding0>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <A>) <internal:def#transEncoding0>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <C>) <B>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <C>) <internal:def#transEncoding1>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <internal:def#transEncoding1>) <internal:def#transEncoding1>)");
			control.add("SubClassOf(<internal:def#transEncoding1> <B>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}

	@Test
	public void testTransitivityEncoding11() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectIntersectionOf(
							factory.getOWLObjectSomeValuesFrom(r, a),
							b),
					factory.getOWLObjectUnionOf(
							factory.getOWLObjectAllValuesFrom(s, c),
							d));
			OWLAxiom ax2 = factory.getOWLTransitiveObjectPropertyAxiom(r);
			OWLAxiom ax3 = factory.getOWLTransitiveObjectPropertyAxiom(s);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			axioms.add(ax3);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, true, true);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(ObjectIntersectionOf(<B> <internal:def#transEncoding2>) ObjectUnionOf(<D> <internal:def#transEncoding0>))");
			control.add("SubClassOf(<internal:def#transEncoding0> ObjectAllValuesFrom(<S> <C>))");
			control.add("SubClassOf(<internal:def#transEncoding0> ObjectAllValuesFrom(<S> <internal:def#transEncoding1>))");
			control.add("SubClassOf(<internal:def#transEncoding1> ObjectAllValuesFrom(<S> <internal:def#transEncoding1>))");
			control.add("SubClassOf(<internal:def#transEncoding1> <C>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <A>) <internal:def#transEncoding2>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <A>) <internal:def#transEncoding3>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <internal:def#transEncoding3>) <internal:def#transEncoding3>)");
			control.add("SubClassOf(<internal:def#transEncoding3> <internal:def#transEncoding2>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testTransitivityEncoding12() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectSomeValuesFrom(r, a),
					factory.getOWLObjectAllValuesFrom(s, b));
			OWLAxiom ax2 = factory.getOWLTransitiveObjectPropertyAxiom(r);
			OWLAxiom ax3 = factory.getOWLTransitiveObjectPropertyAxiom(s);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			axioms.add(ax3);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, true, true);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <A>) <internal:def#transEncoding0>)");
			control.add("SubClassOf(<internal:def#transEncoding0> ObjectAllValuesFrom(<S> <B>))");
			control.add("SubClassOf(<internal:def#transEncoding0> ObjectAllValuesFrom(<S> <internal:def#transEncoding1>))");
			control.add("SubClassOf(<internal:def#transEncoding1> ObjectAllValuesFrom(<S> <internal:def#transEncoding1>))");
			control.add("SubClassOf(<internal:def#transEncoding1> <B>)");
			
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <A>) <internal:def#transEncoding2>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <internal:def#transEncoding2>) <internal:def#transEncoding2>)");
			control.add("SubClassOf(<internal:def#transEncoding2> <internal:def#transEncoding0>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testTransitivityEncodingReusingInternalClasses() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					a,
					factory.getOWLObjectAllValuesFrom(r, b));
			OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(
					c,
					factory.getOWLObjectAllValuesFrom(r, b));
			OWLAxiom ax3 = factory.getOWLTransitiveObjectPropertyAxiom(r);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			axioms.add(ax3);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, true, true);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<A> ObjectAllValuesFrom(<R> <B>))");
			control.add("SubClassOf(<C> ObjectAllValuesFrom(<R> <B>))");
			control.add("SubClassOf(<A> ObjectAllValuesFrom(<R> <internal:def#transEncoding0>))");
			control.add("SubClassOf(<C> ObjectAllValuesFrom(<R> <internal:def#transEncoding0>))");
			control.add("SubClassOf(<internal:def#transEncoding0> ObjectAllValuesFrom(<R> <internal:def#transEncoding0>))");
			control.add("SubClassOf(<internal:def#transEncoding0> <B>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		
		}
	}
	
	@Test
	public void testTransitivityEncodingReusingInternalClasses2() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					a,
					factory.getOWLObjectUnionOf(
							factory.getOWLObjectAllValuesFrom(r, b),
							c
					));
			OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(
					d,
					factory.getOWLObjectUnionOf(
							factory.getOWLObjectAllValuesFrom(r, b),
							e
					));
			OWLAxiom ax3 = factory.getOWLTransitiveObjectPropertyAxiom(r);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			axioms.add(ax3);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, true, true);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<A> ObjectUnionOf(<C> <internal:def#transEncoding0>))");
			control.add("SubClassOf(<D> ObjectUnionOf(<E> <internal:def#transEncoding0>))");
			control.add("SubClassOf(<internal:def#transEncoding0> ObjectAllValuesFrom(<R> <B>))");
			control.add("SubClassOf(<internal:def#transEncoding0> ObjectAllValuesFrom(<R> <internal:def#transEncoding1>))");
			control.add("SubClassOf(<internal:def#transEncoding1> ObjectAllValuesFrom(<R> <internal:def#transEncoding1>))");
			control.add("SubClassOf(<internal:def#transEncoding1> <B>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		
		}
	}
	
	@Test
	public void testTransitivityEncodingReusingInternalClasses3() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectIntersectionOf(
							a,
							factory.getOWLObjectSomeValuesFrom(r, b)),
					c);
			OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(
					factory.getOWLObjectIntersectionOf(
							d,
							factory.getOWLObjectSomeValuesFrom(r, b)),
					e);
			OWLAxiom ax3 = factory.getOWLTransitiveObjectPropertyAxiom(r);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			axioms.add(ax3);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, false, true, true);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(ObjectIntersectionOf(<A> <internal:def#transEncoding0>) <C>)");
			control.add("SubClassOf(ObjectIntersectionOf(<D> <internal:def#transEncoding0>) <E>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <B>) <internal:def#transEncoding0>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <B>) <internal:def#transEncoding1>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<R> <internal:def#transEncoding1>) <internal:def#transEncoding1>)");
			control.add("SubClassOf(<internal:def#transEncoding1> <internal:def#transEncoding0>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		
		}
	}
	
	@Test
	public void testRangeEncoding1() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					a,
					factory.getOWLObjectSomeValuesFrom(r, b));
			OWLAxiom ax2 = factory.getOWLObjectPropertyRangeAxiom(r, c);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, true, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<A> ObjectSomeValuesFrom(<R> <internal:def#rangeIntegClass0>))");
			control.add("SubClassOf(<internal:def#rangeIntegClass0> <B>)");
			control.add("SubClassOf(<internal:def#rangeIntegClass0> <C>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		
		}
	}
	
	@Test
	public void testRangeEncoding2() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					a,
					factory.getOWLObjectSomeValuesFrom(r, b));
			OWLAxiom ax2 = factory.getOWLObjectPropertyRangeAxiom(r, c);
			OWLAxiom ax3 = factory.getOWLObjectPropertyRangeAxiom(s, d);
			OWLAxiom ax4 = factory.getOWLSubObjectPropertyOfAxiom(r, s);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			axioms.add(ax3);
			axioms.add(ax4);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, true, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<A> ObjectSomeValuesFrom(<R> <internal:def#rangeIntegClass0>))");
			control.add("SubClassOf(<internal:def#rangeIntegClass0> <B>)");
			control.add("SubClassOf(<internal:def#rangeIntegClass0> <C>)");
			control.add("SubClassOf(<internal:def#rangeIntegClass0> <D>)");
			control.add("SubObjectPropertyOf(<R> <S>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		
		}
	}
	
	@Test
	public void testRangeEncoding3() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					a,
					factory.getOWLObjectSomeValuesFrom(r, b));
			OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(
					c,
					factory.getOWLObjectSomeValuesFrom(s, d));
			OWLAxiom ax3 = factory.getOWLInverseObjectPropertiesAxiom(r, s);
			OWLAxiom ax4 = factory.getOWLObjectPropertyRangeAxiom(r, e);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			axioms.add(ax3);
			axioms.add(ax4);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, true, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<A> ObjectSomeValuesFrom(<R> <internal:def#rangeIntegClass0>))");
			control.add("SubClassOf(<C> ObjectSomeValuesFrom(<S> <D>))");
			control.add("SubObjectPropertyOf(<S> InverseOf(<R>))");
			control.add("SubObjectPropertyOf(<R> InverseOf(<S>))");
			control.add("SubClassOf(ObjectSomeValuesFrom(InverseOf(<R>) owl:Thing) <E>)");
			control.add("SubClassOf(<internal:def#rangeIntegClass0> <B>)");
			control.add("SubClassOf(<internal:def#rangeIntegClass0> <E>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		
		}
	}
	
	@Test
	public void testRangeEncoding4() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					a,
					factory.getOWLObjectSomeValuesFrom(r, b));
			OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(
					c,
					factory.getOWLObjectSomeValuesFrom(s, d));
			OWLAxiom ax3 = factory.getOWLInverseObjectPropertiesAxiom(r, s);
			OWLAxiom ax4 = factory.getOWLObjectPropertyDomainAxiom(s, e);
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			axioms.add(ax2);
			axioms.add(ax3);
			axioms.add(ax4);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, true, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("SubClassOf(<A> ObjectSomeValuesFrom(<R> <B>))");
			control.add("SubClassOf(<C> ObjectSomeValuesFrom(<S> <D>))");
			control.add("SubObjectPropertyOf(<S> InverseOf(<R>))");
			control.add("SubObjectPropertyOf(<R> InverseOf(<S>))");
			control.add("SubClassOf(ObjectSomeValuesFrom(<S> owl:Thing) <E>)");
			
			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		
		}
	}
	
	@Test
	public void testTautologicalAxioms() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(
					a,
					factory.getOWLThing());
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, true, false, false);
			
			Set<String> actual = new HashSet<String>();
			for (OWLAxiom ax : normalization.getNormalizedOntology()){
				actual.add(ax.toString());
			}

			Set<String> control = new HashSet<String>();

			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		
		}
	}
	
	@Test
	public void complexRoleInclusionsTest() throws Exception{
		OWLNormalization4MORe.resetFreshClassCounter();
		OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(p, b));
		OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(b, factory.getOWLObjectSomeValuesFrom(q, c));
		List<OWLObjectProperty> chain = new ArrayList<OWLObjectProperty>();
		chain.add(p);
		chain.add(q);
		OWLAxiom ax3 = factory.getOWLSubPropertyChainOfAxiom(chain, r);
		OWLAxiom ax4 = factory.getOWLSubObjectPropertyOfAxiom(q, s);
		OWLAxiom ax5 = factory.getOWLObjectPropertyRangeAxiom(p, d);
		OWLAxiom ax6 = factory.getOWLObjectPropertyRangeAxiom(q, e);
		OWLAxiom ax7 = factory.getOWLObjectPropertyRangeAxiom(r, f);
		OWLAxiom ax8 = factory.getOWLObjectPropertyRangeAxiom(s, g);
		
		Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
		axioms.add(ax1);
		axioms.add(ax2);
		axioms.add(ax3);
		axioms.add(ax4);
		axioms.add(ax5);
		axioms.add(ax6);
		axioms.add(ax7);
		axioms.add(ax8);
		
		OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
		
		Set<String> actual = new HashSet<String>();
		OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, true, false, false);
		for (OWLAxiom ax : normalization.getNormalizedOntology()){
			actual.add(ax.toString());
//			System.out.println(ax.toString());
		}
		
		Set<String> control = new HashSet<String>();
		control.add("SubObjectPropertyOf(<Q> <S>)");
		control.add("SubObjectPropertyOf(ObjectPropertyChain( <P> <Q> ) <R>)");
		control.add("SubClassOf(<internal:def#rangeIntegClass0> <D>)");
		control.add("SubClassOf(<A> ObjectSomeValuesFrom(<P> <internal:def#rangeIntegClass0>))");
		control.add("SubClassOf(<internal:def#rangeIntegClass0> <B>)");
		control.add("SubClassOf(<internal:def#rangeIntegClass1> <C>)");
		control.add("SubClassOf(<internal:def#rangeIntegClass1> <E>)");
		control.add("SubClassOf(owl:Thing ObjectAllValuesFrom(<R> <F>))");
		control.add("SubClassOf(<internal:def#rangeIntegClass1> <G>)");
		control.add("SubClassOf(<B> ObjectSomeValuesFrom(<Q> <internal:def#rangeIntegClass1>))");

		TestUtility.checkEqualSets(actual, control);
		
	}
	
	
	
	@Test
	public void complexRoleInclusionsTest2() throws Exception{
		OWLNormalization4MORe.resetFreshClassCounter();
		OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(p, b));
		OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(b, factory.getOWLObjectSomeValuesFrom(q, c));
		List<OWLObjectProperty> chain = new ArrayList<OWLObjectProperty>();
		chain.add(p);
		chain.add(q);
		OWLAxiom ax3 = factory.getOWLSubPropertyChainOfAxiom(chain, r);
		OWLAxiom ax4 = factory.getOWLSubObjectPropertyOfAxiom(q, s);
		OWLAxiom ax5 = factory.getOWLObjectPropertyRangeAxiom(p, d);
		OWLAxiom ax6 = factory.getOWLObjectPropertyRangeAxiom(q, e);
		OWLAxiom ax7 = factory.getOWLObjectPropertyRangeAxiom(r, f);
		OWLAxiom ax8 = factory.getOWLObjectPropertyRangeAxiom(s, g);
		OWLAxiom ax9 = factory.getOWLTransitiveObjectPropertyAxiom(s);
		
		
		Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
		axioms.add(ax1);
		axioms.add(ax2);
		axioms.add(ax3);
		axioms.add(ax4);
		axioms.add(ax5);
		axioms.add(ax6);
		axioms.add(ax7);
		axioms.add(ax8);
		axioms.add(ax9);
		
		OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
		
		Set<String> actual = new HashSet<String>();
		OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, true, false, false);
		for (OWLAxiom ax : normalization.getNormalizedOntology()){
			actual.add(ax.toString());
//			System.out.println(ax.toString());
		}
		
		Set<String> control = new HashSet<String>();
		control.add("SubObjectPropertyOf(<Q> <S>)");
		control.add("SubObjectPropertyOf(ObjectPropertyChain( <P> <Q> ) <R>)");
		control.add("SubClassOf(<internal:def#rangeIntegClass0> <D>)");
		control.add("SubClassOf(<A> ObjectSomeValuesFrom(<P> <internal:def#rangeIntegClass0>))");
		control.add("SubClassOf(<internal:def#rangeIntegClass0> <B>)");
		control.add("SubClassOf(owl:Thing ObjectAllValuesFrom(<R> <F>))");
		control.add("SubClassOf(<B> ObjectSomeValuesFrom(<Q> <internal:def#rangeIntegClass1>))");
		control.add("SubClassOf(<internal:def#rangeIntegClass1> <C>)");
		control.add("SubClassOf(<internal:def#rangeIntegClass1> <E>)");
		control.add("TransitiveObjectProperty(<S>)");
		control.add("SubClassOf(owl:Thing ObjectAllValuesFrom(<S> <G>))");
		
		TestUtility.checkEqualSets(actual, control);
	}
	
	
	@Test
	public void complexRoleInclusionsTest3() throws Exception{
		OWLNormalization4MORe.resetFreshClassCounter();
		OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(p, b));
		OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(b, factory.getOWLObjectSomeValuesFrom(q, c));
		List<OWLObjectProperty> chain = new ArrayList<OWLObjectProperty>();
		chain.add(p);
		chain.add(q);
		OWLAxiom ax3 = factory.getOWLSubPropertyChainOfAxiom(chain, r);
		OWLAxiom ax4 = factory.getOWLSubObjectPropertyOfAxiom(q, s);
		OWLAxiom ax5 = factory.getOWLObjectPropertyRangeAxiom(p, d);
		OWLAxiom ax6 = factory.getOWLObjectPropertyRangeAxiom(q, e);
		OWLAxiom ax7 = factory.getOWLObjectPropertyRangeAxiom(r, f);
		OWLAxiom ax8 = factory.getOWLObjectPropertyRangeAxiom(s, g);
		OWLAxiom ax9 = factory.getOWLTransitiveObjectPropertyAxiom(s);
		
		
		Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
		axioms.add(ax1);
		axioms.add(ax2);
		axioms.add(ax3);
		axioms.add(ax4);
		axioms.add(ax5);
		axioms.add(ax6);
		axioms.add(ax7);
		axioms.add(ax8);
		axioms.add(ax9);
		
		OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
		
		OWLNormalization4MORe normalization = new OWLNormalization4MORe(o, true, true, false);
		try{
			normalization.getNormalizedOntology();
			Assert.assertTrue(false);
		}
		catch (IllegalArgumentException e){
			Assert.assertTrue(true);
		}

	}
}
