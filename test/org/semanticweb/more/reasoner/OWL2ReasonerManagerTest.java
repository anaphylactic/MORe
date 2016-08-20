package org.semanticweb.more.reasoner;

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Level;
import org.junit.Test;
import org.semanticweb.elk.owlapi.ElkReasoner;
import org.semanticweb.elk.owlapi.ElkReasonerFactory;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;
import uk.ac.ox.cs.pagoda.util.Utility_PAGOdA;
import util.TestUtility;

public class OWL2ReasonerManagerTest {

	OWLClass a;
	OWLClass b;
	OWLClass c;
	OWLClass d;
	OWLClass e;
	OWLClass f;
	OWLClass g;
	OWLClass h;
	OWLClass i;
	OWLClass j;
	OWLClass k;
	OWLClass l;
	OWLClass m;
	OWLNamedIndividual o;
	OWLObjectProperty r;
	OWLDataFactory factory;
	OWLOntologyManager manager;
	String iriBase = new File(Utility_PAGOdA.TempDirectory + "ontology.owl").getAbsolutePath();
	String iriPrefix4Entities = "file:/" + iriBase.substring(0, iriBase.lastIndexOf("."));
	String iri = "file:" + iriBase;
	
	Set<OWLEntity> signature;
	OWLAxiom axiom;
	List<Set<OWLEntity>> expectedSolutions;
	Set<OWLEntity> auxSet;
	Set<OWLIndividual> auxSetIndiv;
	Set<OWLClassExpression> auxSetClassExp;
	LinkedList<OWLObjectPropertyExpression> auxList;
	
	
	protected void setUp(){
		factory = new OWLDataFactoryImpl();
		manager = OWLManager.createOWLOntologyManager();
		
		a = factory.getOWLClass(IRI.create(iriPrefix4Entities + "#A"));
		b = factory.getOWLClass(IRI.create(iriPrefix4Entities + "#B"));
		c = factory.getOWLClass(IRI.create(iriPrefix4Entities + "#C"));
		d = factory.getOWLClass(IRI.create(iriPrefix4Entities + "#D"));
		e = factory.getOWLClass(IRI.create(iriPrefix4Entities + "#E"));
		f = factory.getOWLClass(IRI.create(iriPrefix4Entities + "#F"));
		g = factory.getOWLClass(IRI.create(iriPrefix4Entities + "#G"));
		h = factory.getOWLClass(IRI.create(iriPrefix4Entities + "#H"));
		i = factory.getOWLClass(IRI.create(iriPrefix4Entities + "#I"));
		j = factory.getOWLClass(IRI.create(iriPrefix4Entities + "#J"));
		k = factory.getOWLClass(IRI.create(iriPrefix4Entities + "#K"));
		l = factory.getOWLClass(IRI.create(iriPrefix4Entities + "#L"));
		m = factory.getOWLClass(IRI.create(iriPrefix4Entities + "#M"));
		o = factory.getOWLNamedIndividual(IRI.create(iriPrefix4Entities + "#o"));
		r = factory.getOWLObjectProperty(IRI.create(iriPrefix4Entities + "#R"));
		
		Logger_MORe.setLevel(Level.OFF);
	}
	
	@Test
	public void externalOWL2ReasonerTest_withRDFox() throws Exception{
		setUp();
		OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(r, b));
		OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(b, factory.getOWLNothing());//a will be unsat in the lower bound
		
		OWLAxiom ax3 = factory.getOWLSubClassOfAxiom(c, e);
		OWLAxiom ax4 = factory.getOWLSubClassOfAxiom(d, e);
		OWLAxiom ax5 = factory.getOWLSubClassOfAxiom(e, factory.getOWLObjectSomeValuesFrom(r, f));
		OWLAxiom ax6 = factory.getOWLSubClassOfAxiom(c, factory.getOWLObjectAllValuesFrom(r, g));
		OWLAxiom ax7 = factory.getOWLSubClassOfAxiom(d, factory.getOWLObjectAllValuesFrom(r, h));
		OWLAxiom ax8 = factory.getOWLDisjointClassesAxiom(g,h);//c and d are sat but unsat in the lazy UpperBound
		
		OWLAxiom ax9 = factory.getOWLSubClassOfAxiom(i, factory.getOWLObjectUnionOf(j,k));//i is sat and has a gap - and the union will cause use of the lazyUpperStore make this unsat in the trackingstore
		
		OWLAxiom ax10 = factory.getOWLSubClassOfAxiom(l, m);//l is sat and doesn't have a gap
		
		OWLOntology o = manager.createOntology(IRI.create(iri));
		TestUtility.addAxiomsToOntology(o, manager, ax1, ax2, ax3, ax4, ax5, ax6, ax7, ax8, ax9, ax10);
		TestUtility.addDeclarationAxiomsToOntology(o, manager, a, b,c, d, e, f, g, h, i, j, k, l, m, r);
		
		manager.setOntologyDocumentIRI(o, IRI.create(iri));
		manager.saveOntology(o);
		
		boolean integrateRanges = true;
		boolean rewriteInverses = true;
		boolean eliminateForgettableRoles = true;
		boolean useMultiStageMaterialisation = true; 
		boolean useRDFox = true;
		MOReReasonerConfiguration config = new MOReReasonerConfiguration(integrateRanges, rewriteInverses, eliminateForgettableRoles, 
				useMultiStageMaterialisation, useRDFox);
		MOReReasoner more = (MOReReasoner) new MOReReasonerFactory().createReasoner(o, config, new ElkReasonerFactory(), null);
		more.classifyClasses();
		assertTrue(more.owl2reasoner instanceof ElkReasoner);
	}
	
	@Test
	public void externalOWL2ReasonerTest_withoutRDFox() throws Exception{
		setUp();
		OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(r, b));
		OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(b, factory.getOWLNothing());//a will be unsat in the lower bound
		
		OWLAxiom ax3 = factory.getOWLSubClassOfAxiom(c, e);
		OWLAxiom ax4 = factory.getOWLSubClassOfAxiom(d, e);
		OWLAxiom ax5 = factory.getOWLSubClassOfAxiom(e, factory.getOWLObjectSomeValuesFrom(r, f));
		OWLAxiom ax6 = factory.getOWLSubClassOfAxiom(c, factory.getOWLObjectAllValuesFrom(r, g));
		OWLAxiom ax7 = factory.getOWLSubClassOfAxiom(d, factory.getOWLObjectAllValuesFrom(r, h));
		OWLAxiom ax8 = factory.getOWLDisjointClassesAxiom(g,h);//c and d are sat but unsat in the lazy UpperBound
		
		OWLAxiom ax9 = factory.getOWLSubClassOfAxiom(i, factory.getOWLObjectUnionOf(j,k));//i is sat and has a gap - and the union will cause use of the lazyUpperStore make this unsat in the trackingstore
		
		OWLAxiom ax10 = factory.getOWLSubClassOfAxiom(l, m);//l is sat and doesn't have a gap
		
		OWLOntology o = manager.createOntology(IRI.create(iri));
		TestUtility.addAxiomsToOntology(o, manager, ax1, ax2, ax3, ax4, ax5, ax6, ax7, ax8, ax9, ax10);
		TestUtility.addDeclarationAxiomsToOntology(o, manager, a, b,c, d, e, f, g, h, i, j, k, l, m, r);
		
		manager.setOntologyDocumentIRI(o, IRI.create(iri));
		manager.saveOntology(o);
		
		boolean integrateRanges = true;
		boolean rewriteInverses = true;
		boolean eliminateForgettableRoles = true;
		boolean useMultiStageMaterialisation = false; 
		boolean useRDFox = false;
		MOReReasonerConfiguration config = new MOReReasonerConfiguration(integrateRanges, rewriteInverses, eliminateForgettableRoles, 
				useMultiStageMaterialisation, useRDFox);
		MOReReasoner more = (MOReReasoner) new MOReReasonerFactory().createReasoner(o, config, new ElkReasonerFactory(), null);
		more.classifyClasses();
		assertTrue(more.owl2reasoner instanceof ElkReasoner);
	}
	
}
