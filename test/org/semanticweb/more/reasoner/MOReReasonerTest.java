package org.semanticweb.more.reasoner;

import static org.junit.Assert.assertTrue;

import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Level;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.more.visitors.EqualityAxiomVisitor;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.InferenceType;

import util.TestUtility;


public class MOReReasonerTest {

	static OWLOntology ontology;
	static OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
	static String iri_onto;

//	@Test
	public void classifyClassesTest(){
		String oxfordOntoRepository = "http://www.cs.ox.ac.uk/isg/ontologies/UID/";
		String[] ontologies = new String[]{"00001.owl", "00002.owl", "00049.owl", "00350.owl", "00351.owl", "00459.owl", "00772.owl", "00774.owl"};
		try{
			for (String o : ontologies){
				Logger_MORe.setLevel(Level.INFO);
				System.out.println(o);
				iri_onto = oxfordOntoRepository + o;

				Set<OWLAxiom> rtBox = new HashSet<OWLAxiom>();

				ontology = manager.loadOntology(IRI.create(iri_onto));
				EqualityAxiomVisitor visitor = new EqualityAxiomVisitor();
				for (OWLAxiom ax : ontology.getTBoxAxioms(true)){
					if (!visitor.containsEquality(ax))
						rtBox.add(ax);
				}
				for (OWLAxiom ax : ontology.getRBoxAxioms(true)){
					if (!visitor.containsEquality(ax))
						rtBox.add(ax);
				}
				manager.removeOntology(ontology);
				ontology = manager.createOntology(rtBox, IRI.create("RTBox.owl"));

				Logger_MORe.logDebug("\nLoaded ontology: " + iri_onto);

				Reasoner hermit = new Reasoner(ontology);
				hermit.precomputeInferences(InferenceType.CLASS_HIERARCHY);

				MOReReasonerConfiguration[] configs = new MOReReasonerConfiguration[]{
						new MOReReasonerConfiguration(false, false, false, false, true),
						new MOReReasonerConfiguration(true, false, false, false, true),
						new MOReReasonerConfiguration(false, true, false, false, true),
						new MOReReasonerConfiguration(false, false, true, false, true),
						new MOReReasonerConfiguration(true, true, true, false, true),
						new MOReReasonerConfiguration(false, false, false, true, true),
						new MOReReasonerConfiguration(true, false, false, true, true),
						new MOReReasonerConfiguration(false, true, false, true, true),
						new MOReReasonerConfiguration(false, false, true, true, true),
						new MOReReasonerConfiguration(true, true, true, true, true),
						new MOReReasonerConfiguration(true, true, true, true, true),
				};

				Logger_MORe.setLevel(Level.OFF);
				for (MOReReasonerConfiguration config : configs){
					MOReReasoner more = new MOReReasoner(ontology, config);
					more.precomputeInferences(InferenceType.CLASS_HIERARCHY);
					System.out.println("done classifying");
					
					assertTrue(TestUtility.compareClassificationMORe(ontology.getClassesInSignature(true), hermit, more));
					System.out.println("now to reload");

					manager.removeOntology(ontology);
					manager = OWLManager.createOWLOntologyManager();
					ontology = manager.createOntology(rtBox, IRI.create("RTBox.owl"));
					Logger_MORe.logDebug("\nReloaded ontology: " + iri_onto);

				}
				manager.removeOntology(ontology);
				System.out.println("Unloaded");
			}
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
			System.exit(0);
		}

	}


}
