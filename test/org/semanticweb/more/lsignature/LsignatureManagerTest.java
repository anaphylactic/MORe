package org.semanticweb.more.lsignature;

import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Level;
import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.more.reasoner.Statistics;
import org.semanticweb.more.structural.OWLNormalization4MORe;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;
import util.TestUtility;


public class LsignatureManagerTest {

	
	static OWLClass a;
	static OWLClass b;
	static OWLClass c;
	static OWLClass d;
	static OWLClass e;
	static OWLClass f;
	static OWLClass g;
	static OWLClass h;
	static OWLNamedIndividual i;
	static OWLNamedIndividual j;
	static OWLObjectProperty p;
	static OWLObjectProperty q;
	static OWLObjectProperty r;
	static OWLObjectProperty s;
	static OWLObjectProperty t;
	static OWLObjectProperty u;
	static OWLDataFactoryImpl factory;
	
	
	
	@BeforeClass
	public static void setUp(){
		factory = new OWLDataFactoryImpl();
		a = factory.getOWLClass(IRI.create("A"));
		b = factory.getOWLClass(IRI.create("B"));
		c = factory.getOWLClass(IRI.create("C"));
		d = factory.getOWLClass(IRI.create("D"));
		e = factory.getOWLClass(IRI.create("E"));
		f = factory.getOWLClass(IRI.create("F"));
		g = factory.getOWLClass(IRI.create("G"));
		h = factory.getOWLClass(IRI.create("H"));
		i = factory.getOWLNamedIndividual(IRI.create("i"));
		j = factory.getOWLNamedIndividual(IRI.create("i"));
		p = factory.getOWLObjectProperty(IRI.create("P"));
		q = factory.getOWLObjectProperty(IRI.create("Q"));
		r = factory.getOWLObjectProperty(IRI.create("R"));
		s = factory.getOWLObjectProperty(IRI.create("S"));
		t = factory.getOWLObjectProperty(IRI.create("T"));
		u = factory.getOWLObjectProperty(IRI.create("U"));
		
		Logger_MORe.setLevel(Level.OFF);
	}
	
	@Test
	public void basicLsignatureExtractionTest() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(r, b));
			OWLAxiom ax2 = factory.getOWLObjectPropertyRangeAxiom(r, c);
			OWLAxiom ax3 = factory.getOWLSubClassOfAxiom(d, factory.getOWLObjectAllValuesFrom(r, e));
			OWLAxiom ax4 = factory.getOWLSubClassOfAxiom(f, factory.getOWLObjectSomeValuesFrom(p, g));
			OWLAxiom ax5 = factory.getOWLSubClassOfAxiom(h, factory.getOWLObjectAllValuesFrom(s, h));
			OWLAxiom ax6 = factory.getOWLSubObjectPropertyOfAxiom(p, s.getInverseProperty());
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			axioms.add(ax2);			
			axioms.add(ax3);			
			axioms.add(ax4);			
			axioms.add(ax5);			
			axioms.add(ax6);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			LsignatureManager lSigManager = new LsignatureManager(false, false);
			OWLOntology ont = lSigManager.findLsignature(o, LogicFragment.ELK, new Statistics(o, false, false));
			Set<String> actual = new HashSet<String>();
			for (OWLClass c : lSigManager.getLsignatureClasses()){
				actual.add(c.toString());
//				System.out.println(c.toString());				
			}
			for (OWLEntity e : lSigManager.getLsignatureOtherEntities()){
				actual.add(e.toString());
//				System.out.println(e.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("<B>");
			control.add("<C>");
			control.add("<D>");
			control.add("<E>");
			control.add("<G>");
			control.add("<S>");
			control.add("owl:Thing");
			control.add("owl:Nothing");
			
			TestUtility.checkEqualSets(actual, control);
			
			actual = new HashSet<String>();
			for (OWLAxiom ax : ont.getAxioms()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			control = new HashSet<String>();
			for (OWLAxiom ax : o.getAxioms())
				control.add(ax.toString());

			TestUtility.checkEqualSets(actual, control);
			
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		
	}
	
	@Test
	public void lSignatureExtractionRangeIntegrationTest() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(r, b));
			OWLAxiom ax2 = factory.getOWLObjectPropertyRangeAxiom(r, c);
			OWLAxiom ax3 = factory.getOWLSubClassOfAxiom(d, factory.getOWLObjectAllValuesFrom(r, e));
			OWLAxiom ax4 = factory.getOWLSubClassOfAxiom(f, factory.getOWLObjectSomeValuesFrom(p, g));
			OWLAxiom ax5 = factory.getOWLSubClassOfAxiom(h, factory.getOWLObjectAllValuesFrom(s, h));
			OWLAxiom ax6 = factory.getOWLSubObjectPropertyOfAxiom(p, s.getInverseProperty());
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			axioms.add(ax2);			
			axioms.add(ax3);			
			axioms.add(ax4);			
			axioms.add(ax5);			
			axioms.add(ax6);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			LsignatureManager lSigManager = new LsignatureManager(true, false);
			OWLOntology ont = lSigManager.findLsignature(o, LogicFragment.ELK, new Statistics(o, true, false));
			Set<String> actual = new HashSet<String>();
			for (OWLClass c : lSigManager.getLsignatureClasses()){
				actual.add(c.toString());
//				System.out.println(c.toString());				
			}
			for (OWLEntity e : lSigManager.getLsignatureOtherEntities()){
				actual.add(e.toString());
//				System.out.println(e.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("<A>");
			control.add("<B>");
			control.add("<C>");
			control.add("<D>");
			control.add("<E>");
			control.add("<G>");
			control.add("<R>");
			control.add("<S>");
			control.add("owl:Thing");
			control.add("owl:Nothing");
			
			TestUtility.checkEqualSets(actual, control);
			
			actual = new HashSet<String>();
			for (OWLAxiom ax : ont.getAxioms()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			control = new HashSet<String>();
			for (OWLAxiom ax : o.getAxioms())
				control.add(ax.toString());
			control.add("SubClassOf(<internal:def#rangeIntegClass0> <B>)");
			control.add("SubClassOf(<internal:def#rangeIntegClass0> <C>)");
			control.add("SubClassOf(<A> ObjectSomeValuesFrom(<R> <internal:def#rangeIntegClass0>))");
			
			TestUtility.checkEqualSets(actual, control);
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		
	}
	
	@Test
	public void lSignatureExtractionRangeIntegrationTest2() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLClass x = factory.getOWLClass(IRI.create("X"));
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(r, x));
			OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(x, b);
			OWLAxiom ax3 = factory.getOWLSubClassOfAxiom(x, c);
			OWLAxiom ax4 = factory.getOWLSubClassOfAxiom(d, factory.getOWLObjectAllValuesFrom(r, e));
			OWLAxiom ax5 = factory.getOWLSubClassOfAxiom(f, factory.getOWLObjectSomeValuesFrom(p, g));
			OWLAxiom ax6 = factory.getOWLSubClassOfAxiom(h, factory.getOWLObjectAllValuesFrom(s, h));
			OWLAxiom ax7 = factory.getOWLSubObjectPropertyOfAxiom(p, s.getInverseProperty());
			
			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			axioms.add(ax2);			
			axioms.add(ax3);			
			axioms.add(ax4);			
			axioms.add(ax5);			
			axioms.add(ax6);			
			axioms.add(ax7);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			LsignatureManager lSigManager = new LsignatureManager(false, false);
			OWLOntology ont = lSigManager.findLsignature(o, LogicFragment.ELK, new Statistics(o, false, false));
			Set<String> actual = new HashSet<String>();
			for (OWLClass c : lSigManager.getLsignatureClasses()){
				actual.add(c.toString());
//				System.out.println(c.toString());				
			}
			for (OWLEntity e : lSigManager.getLsignatureOtherEntities()){
				actual.add(e.toString());
//				System.out.println(e.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("<A>");
			control.add("<B>");
			control.add("<C>");
			control.add("<E>");
			control.add("<G>");
			control.add("<X>");
			control.add("<R>");
			control.add("<S>");
			control.add("owl:Thing");
			control.add("owl:Nothing");
			
			TestUtility.checkEqualSets(actual, control);
			
			actual = new HashSet<String>();
			for (OWLAxiom ax : ont.getAxioms()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			control = new HashSet<String>();
			for (OWLAxiom ax : o.getAxioms())
				control.add(ax.toString());
			
			TestUtility.checkEqualSets(actual, control);
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		
	}

	
	@Test
	public void lSignatureExtractionInverseRewritingTest() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(r, b));
			OWLAxiom ax2 = factory.getOWLObjectPropertyRangeAxiom(r, c);
			OWLAxiom ax3 = factory.getOWLSubClassOfAxiom(d, factory.getOWLObjectAllValuesFrom(r, e));
			OWLAxiom ax4 = factory.getOWLSubClassOfAxiom(f, factory.getOWLObjectSomeValuesFrom(p, g));
			OWLAxiom ax5 = factory.getOWLSubClassOfAxiom(h, factory.getOWLObjectAllValuesFrom(s, h));
			OWLAxiom ax6 = factory.getOWLSubObjectPropertyOfAxiom(p, s.getInverseProperty());
			

			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			axioms.add(ax2);			
			axioms.add(ax3);			
			axioms.add(ax4);			
			axioms.add(ax5);			
			axioms.add(ax6);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			LsignatureManager lSigManager = new LsignatureManager(false, true);
			OWLOntology ont = lSigManager.findLsignature(o, LogicFragment.ELK, new Statistics(o, true, false));
			Set<String> actual = new HashSet<String>();
			for (OWLClass c : lSigManager.getLsignatureClasses()){
				actual.add(c.toString());
//				System.out.println(c.toString());				
			}
			for (OWLEntity e : lSigManager.getLsignatureOtherEntities()){
				actual.add(e.toString());
//				System.out.println(e.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("<A>");
			control.add("<B>");
			control.add("<C>");
			control.add("<D>");
			control.add("<E>");
			control.add("<F>");
			control.add("<G>");
			control.add("<H>");
			control.add("<P>");
			control.add("<R>");
			control.add("<S>");
			control.add("<NewgsdS>");
			control.add("owl:Thing");
			control.add("owl:Nothing");
			
			TestUtility.checkEqualSets(actual, control);
			
			actual = new HashSet<String>();
			for (OWLAxiom ax : ont.getAxioms()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			control = new HashSet<String>();
			for (OWLAxiom ax : o.getAxioms())
				control.add(ax.toString());
			control.add("SubClassOf(<internal:def#rangeIntegClass0> <B>)");
			control.add("SubClassOf(<internal:def#rangeIntegClass0> <C>)");
			control.add("SubClassOf(<A> ObjectSomeValuesFrom(<R> <internal:def#rangeIntegClass0>))");
			control.add("SubObjectPropertyOf(<P> <NewgsdS>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<NewgsdS> <H>) <H>)");
			
			TestUtility.checkEqualSets(actual, control);
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
	@Test
	public void lSignatureExtractionInverseRewritingTest2() {
		OWLNormalization4MORe.resetFreshClassCounter();
		try {
			
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(r, b));
			OWLAxiom ax2 = factory.getOWLObjectPropertyRangeAxiom(r, c);
			OWLAxiom ax3 = factory.getOWLSubClassOfAxiom(d, factory.getOWLObjectAllValuesFrom(r, e));
			OWLAxiom ax4 = factory.getOWLSubClassOfAxiom(f, factory.getOWLObjectSomeValuesFrom(p, g));
			OWLAxiom ax5 = factory.getOWLSubClassOfAxiom(h, factory.getOWLObjectAllValuesFrom(s, h));
			OWLAxiom ax6 = factory.getOWLSubObjectPropertyOfAxiom(p, s.getInverseProperty());

			Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
			axioms.add(ax1);			
			axioms.add(ax2);			
			axioms.add(ax3);			
			axioms.add(ax4);			
			axioms.add(ax5);			
			axioms.add(ax6);			
			OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(axioms); 
			
			LsignatureManager lSigManager = new LsignatureManager(true, true);
			OWLOntology ont = lSigManager.findLsignature(o, LogicFragment.ELK, new Statistics(o, true, false));
			Set<String> actual = new HashSet<String>();
			for (OWLClass c : lSigManager.getLsignatureClasses()){
				actual.add(c.toString());
//				System.out.println(c.toString());				
			}
			for (OWLEntity e : lSigManager.getLsignatureOtherEntities()){
				actual.add(e.toString());
//				System.out.println(e.toString());				
			}

			Set<String> control = new HashSet<String>();
			control.add("<A>");
			control.add("<B>");
			control.add("<C>");
			control.add("<D>");
			control.add("<E>");
			control.add("<F>");
			control.add("<G>");
			control.add("<H>");
			control.add("<P>");
			control.add("<R>");
			control.add("<S>");
			control.add("<NewgsdS>");
			control.add("owl:Thing");
			control.add("owl:Nothing");
			
			TestUtility.checkEqualSets(actual, control);
			
			actual = new HashSet<String>();
			for (OWLAxiom ax : ont.getAxioms()){
				actual.add(ax.toString());
//				System.out.println(ax.toString());				
			}

			control = new HashSet<String>();
			for (OWLAxiom ax : o.getAxioms())
				control.add(ax.toString());
			control.add("SubClassOf(<internal:def#rangeIntegClass1> <B>)");
			control.add("SubClassOf(<internal:def#rangeIntegClass1> <C>)");
			control.add("SubClassOf(<A> ObjectSomeValuesFrom(<R> <internal:def#rangeIntegClass1>))");
			control.add("SubObjectPropertyOf(<P> <NewgsdS>)");
			control.add("SubClassOf(ObjectSomeValuesFrom(<NewgsdS> <H>) <H>)");
			

			TestUtility.checkEqualSets(actual, control);
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}
}
