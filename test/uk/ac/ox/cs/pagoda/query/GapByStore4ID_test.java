package uk.ac.ox.cs.pagoda.query;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.junit.Test;
import org.semanticweb.more.pagoda.PAGOdAClassificationManager;
import org.semanticweb.more.util.Utility;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;


public class GapByStore4ID_test {

	OWLClass a;
	OWLClass b;
	OWLClass c;
	OWLClass d;
	OWLClass e;
	OWLClass f;
	OWLObjectProperty r;
	OWLObjectProperty s;
	OWLDataProperty t;
	OWLDataProperty u;
	OWLIndividual i;
	OWLIndividual j;
	OWLDataFactory factory;
	OWLOntologyManager manager;
	String iriPrefix4Entities = "file://Users/Ana/Documents/Work/DatalogModules/MORe_2.0/test/ontology";
	String iriPrefix4Ontology = "file:/Users/Ana/Documents/Work/DatalogModules/MORe_2.0/test/ontology";
	
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
		r = factory.getOWLObjectProperty(IRI.create(iriPrefix4Entities + "#R"));
		s = factory.getOWLObjectProperty(IRI.create(iriPrefix4Entities + "#S"));
		t = factory.getOWLDataProperty(IRI.create(iriPrefix4Entities + "#T"));
		u = factory.getOWLDataProperty(IRI.create(iriPrefix4Entities + "#U"));
		i = factory.getOWLNamedIndividual(IRI.create(iriPrefix4Entities + "#I"));
		j = factory.getOWLNamedIndividual(IRI.create(iriPrefix4Entities + "#J"));
	}
	
	@Test
	public void test() throws Exception {
		setUp();
		OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(r, b));
		OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(s, b));
		OWLAxiom ax3 = factory.getOWLSubClassOfAxiom(b, factory.getOWLObjectAllValuesFrom(r.getInverseProperty(), factory.getOWLNothing()));
		OWLAxiom ax4 = factory.getOWLSubClassOfAxiom(b, factory.getOWLObjectAllValuesFrom(s.getInverseProperty(), factory.getOWLNothing()));
		OWLAxiom ax5 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectUnionOf(c,d));
		OWLAxiom ax6 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectUnionOf(c,d), e);
		
		String iri = "file:/Users/Ana/Documents/Work/DatalogModules/MORe_2.0/test/ontology.owl";
		OWLOntology o = manager.createOntology(IRI.create(iri));
		manager.addAxiom(o, ax1);
		manager.addAxiom(o, ax2);
		manager.addAxiom(o, ax3);
		manager.addAxiom(o, ax4);
		manager.addAxiom(o, ax5);
		manager.addAxiom(o, ax6);
		manager.addAxiom(o, factory.getOWLDeclarationAxiom(a));
		manager.addAxiom(o, factory.getOWLDeclarationAxiom(b));
		manager.addAxiom(o, factory.getOWLDeclarationAxiom(c));
		manager.addAxiom(o, factory.getOWLDeclarationAxiom(d));
		manager.addAxiom(o, factory.getOWLDeclarationAxiom(e));
		manager.addAxiom(o, factory.getOWLDeclarationAxiom(r));
		manager.addAxiom(o, factory.getOWLDeclarationAxiom(s));
		
		manager.setOntologyDocumentIRI(o, IRI.create(iri));
		manager.saveOntology(o);
		System.out.println(o.getOntologyID().toString());
		
		Set<OWLClass> classesToClassify = new HashSet<OWLClass>();
		classesToClassify.add(a);
		PAGOdAClassificationManager pagoda = new PAGOdAClassificationManager(o, classesToClassify, ClassificationQueryType.INDIVIDUAL);
		pagoda.classify();

		//expected
		Set<String> lazyGap_Individuals = new HashSet<String>();
		lazyGap_Individuals.add("<http://www.cs.ox.ac.uk/MORe#instantiation0>");
		Set<String> lazyGap_Predicates1 = new HashSet<String>();
		lazyGap_Predicates1.add("<http://www.w3.org/2002/07/owl#Nothing>"); 
		lazyGap_Predicates1.add("<file://Users/Ana/Documents/Work/DatalogModules/MORe_2.0/test/ontology#C>");
		lazyGap_Predicates1.add("<file://Users/Ana/Documents/Work/DatalogModules/MORe_2.0/test/ontology#E>");
		Set<String> lazyGap_Predicates2 = new HashSet<String>();
		lazyGap_Predicates2.add("<http://www.w3.org/2002/07/owl#Nothing>"); 
		lazyGap_Predicates2.add("<file://Users/Ana/Documents/Work/DatalogModules/MORe_2.0/test/ontology#C>");
		lazyGap_Predicates2.add("<file://Users/Ana/Documents/Work/DatalogModules/MORe_2.0/test/ontology#E>");
		Set<String> lazyGap_IndividualsNothing = new HashSet<String>();
		lazyGap_IndividualsNothing.add("<http://www.cs.ox.ac.uk/MORe#instantiation0>");
		
		Set<String> gap_Individuals = new HashSet<String>();
		gap_Individuals.add("<http://www.cs.ox.ac.uk/MORe#instantiation0>");
		Set<String> gap_Predicates = new HashSet<String>();
		gap_Predicates.add("<http://www.w3.org/2002/07/owl#Nothing>"); 
		gap_Predicates.add("<file://Users/Ana/Documents/Work/DatalogModules/MORe_2.0/test/ontology#C>");
		gap_Predicates.add("<file://Users/Ana/Documents/Work/DatalogModules/MORe_2.0/test/ontology#D>");
		gap_Predicates.add("<file://Users/Ana/Documents/Work/DatalogModules/MORe_2.0/test/ontology#E>");
		Set<String> gap_IndividualsNothing = new HashSet<String>();
		gap_IndividualsNothing.add("<http://www.cs.ox.ac.uk/MORe#instantiation0>");
		
		
		int counter = 0;
		for (GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly gap : pagoda.getGaps()){
			if (counter == 0){
				assert(Utility.compareCollections(gap.getNamedIndividualsWithGap(), lazyGap_Individuals));
				assert(Utility.compareCollections(gap.getNamedInstancesOfNothing(), lazyGap_IndividualsNothing));
				assert(Utility.compareCollections(gap.getPredicatesWithGap(), lazyGap_Predicates1) || 
						Utility.compareCollections(gap.getPredicatesWithGap(), lazyGap_Predicates2));
				counter++;
			}
			else{
				assert(Utility.compareCollections(gap.getNamedIndividualsWithGap(), gap_Individuals));
				assert(Utility.compareCollections(gap.getNamedInstancesOfNothing(), gap_IndividualsNothing));
				assert(Utility.compareCollections(gap.getPredicatesWithGap(), gap_Predicates));
				counter++;
			}
		}
		
	}

}
