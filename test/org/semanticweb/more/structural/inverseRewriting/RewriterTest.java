package org.semanticweb.more.structural.inverseRewriting;

import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Level;
import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.more.structural.OWLNormalization4MORe;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;
import util.TestUtility;


public class RewriterTest {

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
	}


	@Test
	public void testInverseRewriting1() throws OWLOntologyCreationException{
		Logger_MORe.setLevel(Level.OFF);
		
		OWLNormalization4MORe.resetFreshClassCounter();
		
		OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(r.getInverseProperty(), b));
		OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(b, factory.getOWLObjectSomeValuesFrom(r, c));
		OWLAxiom ax3 = factory.getOWLFunctionalObjectPropertyAxiom(r);

		Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
		axioms.add(ax1);
		axioms.add(ax2);
		axioms.add(ax3);
		OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 


		OWLNormalization4MORe normalisation = new OWLNormalization4MORe(o, true, true, true);
		Set<OWLAxiom> normalAxioms = normalisation.getNormalizedOntology();

		Set<SortedGCI> sorted=normalisation.getSortedGCIs();
		Set<String> actual = new HashSet<String>();
		Rewriter rewriter = new Rewriter(normalAxioms, sorted);
		for (OWLAxiom ax : rewriter.getRewrittenOntology()){
			actual.add(ax.toString());
//			System.out.println(ax.toString());
		}
		
		Set<String> control = new HashSet<String>();
		control.add("SubClassOf(owl:Thing ObjectMaxCardinality(1 <R> owl:Thing))");
		control.add("SubClassOf(<A> ObjectSomeValuesFrom(InverseOf(<R>) <B>))");
		control.add("SubClassOf(<B> ObjectSomeValuesFrom(<R> <C>))");
		
		TestUtility.checkEqualSets(actual, control);
		
	}

	@Test
	public void testInverseRewriting2() throws OWLOntologyCreationException{
		Logger_MORe.setLevel(Level.OFF);
		
		OWLNormalization4MORe.resetFreshClassCounter();
		
		OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(r, b));
		OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(s, c));
		OWLAxiom ax3 = factory.getOWLFunctionalObjectPropertyAxiom(t.getInverseProperty());
		OWLAxiom ax4 = factory.getOWLSubObjectPropertyOfAxiom(r, t.getInverseProperty());
		OWLAxiom ax5 = factory.getOWLSubObjectPropertyOfAxiom(s, t.getInverseProperty());
		OWLAxiom ax6 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectIntersectionOf(b,c), d);
		OWLAxiom ax7 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectSomeValuesFrom(r, d), b);

		Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
		axioms.add(ax1);
		axioms.add(ax2);
		axioms.add(ax3);
		axioms.add(ax4);
		axioms.add(ax5);
		axioms.add(ax6);
		axioms.add(ax7);
		OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 


		OWLNormalization4MORe normalisation = new OWLNormalization4MORe(o, true, true, true);
		Set<OWLAxiom> normalAxioms = normalisation.getNormalizedOntology();

		Set<SortedGCI> sorted=normalisation.getSortedGCIs();
		Set<String> actual = new HashSet<String>();
		Rewriter rewriter = new Rewriter(normalAxioms, sorted);
		for (OWLAxiom ax : rewriter.getRewrittenOntology()){
			actual.add(ax.toString());
//			System.out.println(ax.toString());
		}
		
		Set<String> control = new HashSet<String>();
		control.add("SubObjectPropertyOf(<S> <NewgsdT>)");
		control.add("SubClassOf(owl:Thing ObjectMaxCardinality(1 <NewgsdT> owl:Thing))");
		control.add("SubObjectPropertyOf(<R> <NewgsdT>)");
		control.add("SubClassOf(ObjectIntersectionOf(<B> <C>) <D>)");
		control.add("SubClassOf(ObjectSomeValuesFrom(<R> <D>) <B>)");
		control.add("SubClassOf(<A> ObjectSomeValuesFrom(<S> <C>))");
		control.add("SubClassOf(<A> ObjectSomeValuesFrom(<R> <B>))");
		
		TestUtility.checkEqualSets(actual, control);
		
	}

	@Test
	public void testInverseRewriting3() throws OWLOntologyCreationException{
		Logger_MORe.setLevel(Level.OFF);
		
		OWLNormalization4MORe.resetFreshClassCounter();
		
		OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectAllValuesFrom(s, b));
		OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(b, factory.getOWLObjectSomeValuesFrom(r, c));
		OWLAxiom ax3 = factory.getOWLDisjointClassesAxiom(c,d);
		OWLAxiom ax4 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectSomeValuesFrom(s, b), d);
		OWLAxiom ax5 = factory.getOWLSubObjectPropertyOfAxiom(r, s.getInverseProperty());
		
		Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
		axioms.add(ax1);
		axioms.add(ax2);
		axioms.add(ax3);
		axioms.add(ax4);
		axioms.add(ax5);
		OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 


		OWLNormalization4MORe normalisation = new OWLNormalization4MORe(o, true, true, true);
		Set<OWLAxiom> normalAxioms = normalisation.getNormalizedOntology();

		Set<SortedGCI> sorted=normalisation.getSortedGCIs();
		Set<String> actual = new HashSet<String>();
		Rewriter rewriter = new Rewriter(normalAxioms, sorted);
		for (OWLAxiom ax : rewriter.getRewrittenOntology()){
			actual.add(ax.toString());
//			System.out.println(ax.toString());
		}
		
		Set<String> control = new HashSet<String>();
		control.add("SubClassOf(<B> ObjectAllValuesFrom(<NewgsdS> <D>))");
		control.add("SubClassOf(<B> ObjectSomeValuesFrom(<R> <C>))");
		control.add("SubClassOf(ObjectSomeValuesFrom(<NewgsdS> <A>) <B>)");
		control.add("SubClassOf(ObjectIntersectionOf(<C> <D>) owl:Nothing)");
		control.add("SubObjectPropertyOf(<R> <NewgsdS>)");
		
		TestUtility.checkEqualSets(actual, control);
		
	}
	
	
	@Test
	public void testInverseRewriting4() throws OWLOntologyCreationException{
		Logger_MORe.setLevel(Level.OFF);
		
		OWLNormalization4MORe.resetFreshClassCounter();
		
		OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectAllValuesFrom(s, b));
		OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(b, factory.getOWLObjectSomeValuesFrom(r, c));
		OWLAxiom ax3 = factory.getOWLDisjointClassesAxiom(c,d);
		OWLAxiom ax4 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectSomeValuesFrom(s, b), d);
		OWLAxiom ax5 = factory.getOWLSubObjectPropertyOfAxiom(r, s.getInverseProperty());
		OWLAxiom ax6 = factory.getOWLClassAssertionAxiom(a, i);
		OWLAxiom ax7 = factory.getOWLObjectPropertyAssertionAxiom(s, i, j);
		

		Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
		axioms.add(ax1);
		axioms.add(ax2);
		axioms.add(ax3);
		axioms.add(ax4);
		axioms.add(ax5);
		axioms.add(ax6);
		axioms.add(ax7);
		OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 


		OWLNormalization4MORe normalisation = new OWLNormalization4MORe(o, true, true, true);
		Set<OWLAxiom> normalAxioms = normalisation.getNormalizedOntology();

		Set<SortedGCI> sorted=normalisation.getSortedGCIs();
		Set<String> actual = new HashSet<String>();
		Rewriter rewriter = new Rewriter(normalAxioms, sorted);
		for (OWLAxiom ax : rewriter.getRewrittenOntology()){
			actual.add(ax.toString());
//			System.out.println(ax.toString());
		}
		
		Set<String> control = new HashSet<String>();
		control.add("SubClassOf(<B> ObjectAllValuesFrom(<NewgsdS> <D>))");
		control.add("SubClassOf(ObjectSomeValuesFrom(<S> <B>) <D>)");
		control.add("SubClassOf(<B> ObjectSomeValuesFrom(<R> <C>))");
		control.add("SubClassOf(ObjectSomeValuesFrom(<NewgsdS> <A>) <B>)");
		control.add("SubClassOf(<A> ObjectAllValuesFrom(<S> <B>))");
		control.add("SubClassOf(ObjectIntersectionOf(<C> <D>) owl:Nothing)");
		control.add("SubObjectPropertyOf(<R> <NewgsdS>)");
		control.add("SubObjectPropertyOf(<NewgsdR> <S>)");
		control.add("ClassAssertion(<A> <i>)");
		control.add("ObjectPropertyAssertion(<NewgsdS> <i> <i>)");
		control.add("ObjectPropertyAssertion(<S> <i> <i>)");

		TestUtility.checkEqualSets(actual, control);
		
	}
	
	@Test
	public void testInverseRewriting5() throws OWLOntologyCreationException{
		Logger_MORe.setLevel(Level.OFF);
		
		OWLNormalization4MORe.resetFreshClassCounter();
		
		OWLAxiom ax1 = factory.getOWLSymmetricObjectPropertyAxiom(r);
		OWLAxiom ax2 = factory.getOWLTransitiveObjectPropertyAxiom(r);
		OWLAxiom ax3 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(r, b));
		OWLAxiom ax4 = factory.getOWLSubClassOfAxiom(a, c);
		OWLAxiom ax5 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectSomeValuesFrom(r.getInverseProperty(), c), d);
		
		Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
		axioms.add(ax1);
		axioms.add(ax2);
		axioms.add(ax3);
		axioms.add(ax4);
		axioms.add(ax5);
		OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 


		OWLNormalization4MORe normalisation = new OWLNormalization4MORe(o, true, true, true);
		Set<OWLAxiom> normalAxioms = normalisation.getNormalizedOntology();

		
		Set<SortedGCI> sorted=normalisation.getSortedGCIs();
		Set<String> actual = new HashSet<String>();
		Rewriter rewriter = new Rewriter(normalAxioms, sorted);
		for (OWLAxiom ax : rewriter.getRewrittenOntology()){
			actual.add(ax.toString());
//			System.out.println(ax.toString());
		}
		
		Set<String> control = new HashSet<String>();
		control.add("SubObjectPropertyOf(<NewgsdR> <R>)");
		control.add("SubObjectPropertyOf(<R> <NewgsdR>)");

		control.add("SubClassOf(<C> ObjectAllValuesFrom(<R> <internal:def#transEncoding0>))");
		control.add("SubClassOf(<C> ObjectAllValuesFrom(<R> <D>))");
		control.add("SubClassOf(<C> ObjectAllValuesFrom(<NewgsdR> <internal:def#transEncoding1>))");

		control.add("SubClassOf(ObjectSomeValuesFrom(<NewgsdR> <C>) <D>)");
		control.add("SubClassOf(ObjectSomeValuesFrom(<R> <C>) <internal:def#transEncoding1>)");
		control.add("SubClassOf(ObjectSomeValuesFrom(<NewgsdR> <C>) <internal:def#transEncoding0>)");

		control.add("SubClassOf(ObjectSomeValuesFrom(<NewgsdR> <internal:def#transEncoding0>) <internal:def#transEncoding0>)");
		control.add("SubClassOf(<internal:def#transEncoding0> ObjectAllValuesFrom(<R> <internal:def#transEncoding0>))");
		control.add("SubClassOf(<internal:def#transEncoding1> ObjectAllValuesFrom(<NewgsdR> <internal:def#transEncoding1>))");
		control.add("SubClassOf(ObjectSomeValuesFrom(<R> <internal:def#transEncoding1>) <internal:def#transEncoding1>)");
		
		control.add("SubClassOf(<internal:def#transEncoding1> <D>)");
		control.add("SubClassOf(<internal:def#transEncoding0> <D>)");
		
		control.add("SubClassOf(<A> ObjectSomeValuesFrom(<R> <B>))");
		control.add("SubClassOf(<A> <C>)");

		TestUtility.checkEqualSets(actual, control);
		
	}
	


}
