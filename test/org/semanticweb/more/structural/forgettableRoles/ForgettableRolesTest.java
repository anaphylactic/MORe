package org.semanticweb.more.structural.forgettableRoles;

import static org.junit.Assert.assertTrue;

import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Level;
import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.more.util.Utility;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;


public class ForgettableRolesTest {

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
	public void test1() {
		Logger_MORe.setLevel(Level.OFF);
		
		try {
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(r, b));
			OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(b, factory.getOWLObjectSomeValuesFrom(s, c));
			OWLAxiom ax3 = factory.getOWLSubClassOfAxiom(c, factory.getOWLObjectAllValuesFrom(s, d));
			OWLAxiom ax4 = factory.getOWLSymmetricObjectPropertyAxiom(s);

			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			axioms.add(ax2);			
			axioms.add(ax3);			
			axioms.add(ax4);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 

			ForgettableRoles rewriter = new ForgettableRoles();
			if (rewriter.rewrite(o) != null){
				Set<String> actual = new HashSet<String>();
				for (OWLAxiom ax : rewriter.rewrittenAxioms){
					actual.add(ax.toString());
					//				System.out.println(ax.toString());
				}

				Set<String> expected = new HashSet<String>();
				expected.add("SymmetricObjectProperty(<S>)");
				expected.add("SubClassOf(<C> ObjectAllValuesFrom(<S> <D>))");
				expected.add("SubClassOf(<B> ObjectSomeValuesFrom(<S> <C>))");
				assertTrue(Utility.compareCollections(actual, expected));
			}
			else 
				assertTrue(false);

		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}

	@Test
	public void test2() {
		Logger_MORe.setLevel(Level.OFF);
		
		try {
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(r, factory.getOWLObjectSomeValuesFrom(s, b)));
			OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectSomeValuesFrom(r, c), d);

			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			axioms.add(ax2);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 

			ForgettableRoles rewriter = new ForgettableRoles();
			rewriter.rewrite(o);
			if (rewriter.rewrite(o) != null){
				Set<String> actual = new HashSet<String>();
				for (OWLAxiom ax : rewriter.rewrittenAxioms){
					actual.add(ax.toString());
					//				System.out.println(ax.toString());
				}

				Set<String> expected = new HashSet<String>();
				expected.add("SubClassOf(ObjectSomeValuesFrom(<R> <C>) <D>)");
				expected.add("SubClassOf(<A> ObjectSomeValuesFrom(<R> owl:Thing))");
				assertTrue(Utility.compareCollections(actual, expected));

			}
			else 
				assertTrue(false);

		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}

	@Test
	public void test3() {
		Logger_MORe.setLevel(Level.OFF);
		
		try {
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(r, factory.getOWLObjectSomeValuesFrom(s, b)));
			OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectSomeValuesFrom(r, c), d);
			OWLAxiom ax3 = factory.getOWLObjectPropertyDomainAxiom(s, e);

			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			axioms.add(ax2);			
			axioms.add(ax3);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 

			ForgettableRoles rewriter = new ForgettableRoles();
			rewriter.rewrite(o);
			if (rewriter.rewrite(o) != null){
				Set<String> actual = new HashSet<String>();
				for (OWLAxiom ax : rewriter.rewrittenAxioms){
					actual.add(ax.toString());
					//				System.out.println(ax.toString());
				}

				Set<String> expected = new HashSet<String>();
				expected.add("ObjectPropertyDomain(<S> <E>)");
				expected.add("SubClassOf(ObjectSomeValuesFrom(<R> <C>) <D>)");
				expected.add("SubClassOf(<A> ObjectSomeValuesFrom(<R> <E>))");
				assertTrue(Utility.compareCollections(actual, expected));
			}
			else 
				assertTrue(false);
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}

	@Test
	public void test4() {
		Logger_MORe.setLevel(Level.OFF);
		
		try {
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(r, factory.getOWLObjectSomeValuesFrom(s, b)));
			OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectSomeValuesFrom(r, c), d);
			OWLAxiom ax3 = factory.getOWLInverseObjectPropertiesAxiom(p, s);
			OWLAxiom ax4 = factory.getOWLObjectPropertyRangeAxiom(p, e);

			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			axioms.add(ax2);			
			axioms.add(ax3);			
			axioms.add(ax4);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 

			ForgettableRoles rewriter = new ForgettableRoles();
			rewriter.rewrite(o);
			if (rewriter.rewrite(o) != null){
				Set<String> actual = new HashSet<String>();
				for (OWLAxiom ax : rewriter.rewrittenAxioms){
					actual.add(ax.toString());
					//				System.out.println(ax.toString());
				}

				Set<String> expected = new HashSet<String>();
				expected.add("SubClassOf(ObjectSomeValuesFrom(<R> <C>) <D>)");
				expected.add("SubClassOf(<A> ObjectSomeValuesFrom(<R> <E>))");
				assertTrue(Utility.compareCollections(actual, expected));
			}
			else 
				assertTrue(false);

		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}

	@Test
	public void test5() {
		Logger_MORe.setLevel(Level.OFF);
		
		try {
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(r, factory.getOWLObjectSomeValuesFrom(s, b)));
			OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectSomeValuesFrom(r, c), d);
			OWLAxiom ax3 = factory.getOWLInverseObjectPropertiesAxiom(p, s);
			OWLAxiom ax4 = factory.getOWLObjectPropertyRangeAxiom(p, e);
			OWLAxiom ax5 = factory.getOWLSubObjectPropertyOfAxiom(s, t);
			OWLAxiom ax6 = factory.getOWLObjectPropertyDomainAxiom(t, factory.getOWLObjectIntersectionOf(f, factory.getOWLObjectSomeValuesFrom(q, g)));
			//domains very rarely include existential restrictions, and even less nested ones; if they do, they will be process in the axiom itself, but NOT in the table that matches 
			//'almost superfluous' roles with their domains. This can be improved, but it's an unlikely case, and it's still correct  


			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			axioms.add(ax2);			
			axioms.add(ax3);			
			axioms.add(ax4);			
			axioms.add(ax5);			
			axioms.add(ax6);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 

			ForgettableRoles rewriter = new ForgettableRoles();
			rewriter.rewrite(o);
			if (rewriter.rewrite(o) != null){
				Set<String> actual = new HashSet<String>();
				for (OWLAxiom ax : rewriter.rewrittenAxioms){
					actual.add(ax.toString());
					//				System.out.println(ax.toString());
				}

				Set<String> expected = new HashSet<String>();
				expected.add("SubClassOf(ObjectSomeValuesFrom(<R> <C>) <D>)");
				expected.add("SubClassOf(<A> ObjectSomeValuesFrom(<R> ObjectIntersectionOf(<E> <F> ObjectSomeValuesFrom(<Q> <G>))))");
				expected.add("ObjectPropertyDomain(<T> <F>)");
				assertTrue(Utility.compareCollections(actual, expected));
			}
			else 
				assertTrue(false);

		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}

	@Test
	public void test6() {
		Logger_MORe.setLevel(Level.OFF);
		try {
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectMinCardinality(2, r, factory.getOWLObjectSomeValuesFrom(s, b)));
			OWLAxiom ax2 = factory.getOWLObjectPropertyDomainAxiom(s, c);
			OWLAxiom ax3 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectSomeValuesFrom(r, c), d);

			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			axioms.add(ax2);			
			axioms.add(ax3);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 

			ForgettableRoles rewriter = new ForgettableRoles();
			rewriter.rewrite(o);
			if (rewriter.rewrite(o) != null){
				Set<String> actual = new HashSet<String>();
				for (OWLAxiom ax : rewriter.rewrittenAxioms){
					actual.add(ax.toString());
					//				System.out.println(ax.toString());
				}

				Set<String> expected = new HashSet<String>();
				expected.add("SubClassOf(ObjectSomeValuesFrom(<R> <C>) <D>)");
				expected.add("SubClassOf(<A> ObjectMinCardinality(2 <R> <C>))");
				expected.add("ObjectPropertyDomain(<S> <C>)");
				assertTrue(Utility.compareCollections(actual, expected));
			}
			else 
				assertTrue(false);
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}

	@Test
	public void test7() {
		Logger_MORe.setLevel(Level.OFF);
		
		try {
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectMinCardinality(2, r, factory.getOWLObjectSomeValuesFrom(t, b)));
			OWLAxiom ax2 = factory.getOWLSubObjectPropertyOfAxiom(r, s.getInverseProperty());
			OWLAxiom ax3 = factory.getOWLSubObjectPropertyOfAxiom(s, q.getInverseProperty());
			OWLAxiom ax4 = factory.getOWLSubObjectPropertyOfAxiom(q, p);
			OWLAxiom ax5 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectMinCardinality(4, p), d);


			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			axioms.add(ax2);			
			axioms.add(ax3);
			axioms.add(ax4);			
			axioms.add(ax5);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 

			ForgettableRoles rewriter = new ForgettableRoles();
			rewriter.rewrite(o);
			if (rewriter.rewrite(o) != null){
				Set<String> actual = new HashSet<String>();
				for (OWLAxiom ax : rewriter.rewrittenAxioms){
					actual.add(ax.toString());
					//				System.out.println(ax.toString());
				}

				Set<String> expected = new HashSet<String>();
				expected.add("SubClassOf(<A> ObjectMinCardinality(2 <R> owl:Thing))");
				expected.add("SubObjectPropertyOf(<R> InverseOf(<S>))");
				expected.add("SubObjectPropertyOf(<S> InverseOf(<Q>))");
				expected.add("SubObjectPropertyOf(<Q> <P>)");
				expected.add("SubClassOf(ObjectMinCardinality(4 <P> owl:Thing) <D>)");
				assertTrue(Utility.compareCollections(actual, expected));
			}
			else 
				assertTrue(false);

		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}

	@Test
	public void test8() {
		Logger_MORe.setLevel(Level.OFF);
		try {
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectMinCardinality(2, r, factory.getOWLObjectSomeValuesFrom(t, b)));
			OWLAxiom ax2 = factory.getOWLSubObjectPropertyOfAxiom(r, s.getInverseProperty());
			OWLAxiom ax3 = factory.getOWLSubObjectPropertyOfAxiom(s, p);
			OWLAxiom ax4 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectMaxCardinality(4, p), d);//top -> minCard 5P.top or D


			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			axioms.add(ax2);			
			axioms.add(ax3);
			axioms.add(ax4);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 

			ForgettableRoles rewriter = new ForgettableRoles();
			rewriter.rewrite(o);
			if (rewriter.rewrite(o) != null){
				Set<String> actual = new HashSet<String>();
				for (OWLAxiom ax : rewriter.rewrittenAxioms){
					actual.add(ax.toString());
					//				System.out.println(ax.toString());
				}
				Set<String> expected = new HashSet<String>();
				assertTrue(Utility.compareCollections(actual, expected));
			}
			else 
				assertTrue(false);
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}

	@Test
	public void test9() {
		Logger_MORe.setLevel(Level.OFF);
		
		try {
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectMinCardinality(2, r, factory.getOWLObjectSomeValuesFrom(t, b)));
			OWLAxiom ax2 = factory.getOWLSubObjectPropertyOfAxiom(r, s.getInverseProperty());
			OWLAxiom ax3 = factory.getOWLSubObjectPropertyOfAxiom(s, p);
			OWLAxiom ax4 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectExactCardinality(4, p), d);//minCard 4P. top -> minCard 5P.top or D


			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			axioms.add(ax2);			
			axioms.add(ax3);
			axioms.add(ax4);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 

			ForgettableRoles rewriter = new ForgettableRoles();
			rewriter.rewrite(o);
			if (rewriter.rewrite(o) != null){
				Set<String> actual = new HashSet<String>();
				for (OWLAxiom ax : rewriter.rewrittenAxioms){
					actual.add(ax.toString());
					//				System.out.println(ax.toString());
				}

				Set<String> expected = new HashSet<String>();
				expected.add("SubObjectPropertyOf(<S> <P>)");
				expected.add("SubObjectPropertyOf(<R> InverseOf(<S>))");
				expected.add("SubClassOf(ObjectExactCardinality(4 <P> owl:Thing) <D>)");
				assertTrue(Utility.compareCollections(actual, expected));
			}
			else 
				assertTrue(false);

		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}

	@Test
	public void test10() {
		Logger_MORe.setLevel(Level.OFF);
		
		try {
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectMinCardinality(2, r, factory.getOWLObjectSomeValuesFrom(t, b)));
			OWLAxiom ax2 = factory.getOWLSubObjectPropertyOfAxiom(r, p.getInverseProperty());
			OWLAxiom ax3 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectExactCardinality(4, p, factory.getOWLObjectAllValuesFrom(t, e)), d);//all T. E -> __    is   top -> some R. not E or __      so contains negation


			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			axioms.add(ax2);			
			axioms.add(ax3);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 

			ForgettableRoles rewriter = new ForgettableRoles();
			rewriter.rewrite(o);
			if (rewriter.rewrite(o) != null)
				assertTrue(false);

		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}

	@Test
	public void test11() {
		Logger_MORe.setLevel(Level.OFF);
		
		try {
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectMinCardinality(2, r, factory.getOWLObjectSomeValuesFrom(t, b)));
			OWLAxiom ax2 = factory.getOWLSubObjectPropertyOfAxiom(r, p.getInverseProperty());
			OWLAxiom ax3 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectExactCardinality(4, p, factory.getOWLObjectSomeValuesFrom(t, e)), d);


			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			axioms.add(ax2);			
			axioms.add(ax3);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 

			ForgettableRoles rewriter = new ForgettableRoles();
			rewriter.rewrite(o);
			if (rewriter.rewrite(o) != null){
				Set<String> actual = new HashSet<String>();
				for (OWLAxiom ax : rewriter.rewrittenAxioms){
					actual.add(ax.toString());
					//					System.out.println(ax.toString());
				}
				Set<String> expected = new HashSet<String>();
				expected.add("SubClassOf(ObjectExactCardinality(4 <P> ObjectSomeValuesFrom(<T> <E>)) <D>)");
				expected.add("SubObjectPropertyOf(<R> InverseOf(<P>))");
				assertTrue(Utility.compareCollections(actual, expected));
			}
			else 
				assertTrue(false);

		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}

	@Test
	public void test12() {
		Logger_MORe.setLevel(Level.OFF);
		
		try {
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectSomeValuesFrom(r, factory.getOWLObjectMaxCardinality(2, s)), b);
			OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectSomeValuesFrom(p, factory.getOWLObjectMaxCardinality(2, q)), b);
			OWLAxiom ax3 = factory.getOWLObjectPropertyDomainAxiom(q, c);


			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			axioms.add(ax2);			
			axioms.add(ax3);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 

			ForgettableRoles rewriter = new ForgettableRoles();
			rewriter.rewrite(o);
			if (rewriter.rewrite(o) != null){
				Set<String> actual = new HashSet<String>();
				for (OWLAxiom ax : rewriter.rewrittenAxioms){
					actual.add(ax.toString());
					//					System.out.println(ax.toString());
				}

				Set<String> expected = new HashSet<String>();
				expected.add("SubClassOf(ObjectSomeValuesFrom(<R> owl:Nothing) <B>)");
				expected.add("SubClassOf(ObjectSomeValuesFrom(<P> ObjectComplementOf(<C>)) <B>)");
				expected.add("ObjectPropertyDomain(<Q> <C>)");
				assertTrue(Utility.compareCollections(actual, expected));
			}
			else 
				assertTrue(false);
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}

	@Test
	public void test13() {
		Logger_MORe.setLevel(Level.OFF);
		
		try {
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(r, b));
			OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(c, factory.getOWLObjectSomeValuesFrom(s, d));
			OWLAxiom ax3 = factory.getOWLSubClassOfAxiom(e, factory.getOWLObjectAllValuesFrom(s.getInverseProperty(), f));
			OWLAxiom ax4 = factory.getOWLSubClassOfAxiom(g, factory.getOWLObjectAllValuesFrom(r, e));
			OWLAxiom ax5 = factory.getOWLSubObjectPropertyOfAxiom(s, r);


			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			axioms.add(ax2);			
			axioms.add(ax3);
			axioms.add(ax4);
			axioms.add(ax5);
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 

			ForgettableRoles rewriter = new ForgettableRoles();
			rewriter.rewrite(o);
			if (rewriter.rewrite(o) != null){
				Set<String> actual = new HashSet<String>();
				for (OWLAxiom ax : rewriter.rewrittenAxioms){
					actual.add(ax.toString());
					//				System.out.println(ax.toString());
				}
				Set<String> expected = new HashSet<String>();
				expected.add("SubClassOf(<C> ObjectSomeValuesFrom(<S> <D>))");
				expected.add("SubClassOf(<E> ObjectAllValuesFrom(InverseOf(<S>) <F>))");
				expected.add("SubClassOf(<G> ObjectAllValuesFrom(<R> <E>))");
				expected.add("SubObjectPropertyOf(<S> <R>)");
				assertTrue(Utility.compareCollections(actual, expected));
			}
			else 
				assertTrue(false);

		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
}
