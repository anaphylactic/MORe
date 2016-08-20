package org.semanticweb.more.pagoda;

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Level;
import org.junit.Test;
import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.more.util.Utility;
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
import uk.ac.ox.cs.pagoda.query.QueryRecord;
import uk.ac.ox.cs.pagoda.util.Utility_PAGOdA;
import util.TestUtility;


public class PAGOdAClassificationManagerTest {

//
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
			
			
		}
		
		@Test
		public void lazyMaterialisationTest() throws Exception{
			Logger_MORe.setLevel(Level.OFF);

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
			
			Set<OWLClass> classesToClassify = new HashSet<OWLClass>();
			classesToClassify.add(a);
			classesToClassify.add(c);
			classesToClassify.add(d);
			classesToClassify.add(i);
			classesToClassify.add(l);
			
			PAGOdAClassificationManager pagoda = new PAGOdAClassificationManager(o, classesToClassify);
			
			Set<String> axiomsActual= new HashSet<String>();
			for (OWLAxiom ax : pagoda.classify().getAxioms()){
				axiomsActual.add(ax.toString());
			}
			Set<String> axiomsExpected = new HashSet<String>();
			axiomsExpected.add("SubClassOf(<" + iriPrefix4Entities + "#C> <" + iriPrefix4Entities + "#E>)");
			axiomsExpected.add("SubClassOf(<" + iriPrefix4Entities + "#C> ObjectAllValuesFrom(<" + iriPrefix4Entities + "#R> <" + iriPrefix4Entities + "#G>))");
			axiomsExpected.add("SubClassOf(ObjectIntersectionOf(<" + iriPrefix4Entities + "#G> <" + iriPrefix4Entities + "#H>) owl:Nothing)");
			axiomsExpected.add("SubClassOf(<" + iriPrefix4Entities + "#D> <" + iriPrefix4Entities + "#E>)");
			axiomsExpected.add("SubClassOf(<" + iriPrefix4Entities + "#D> ObjectAllValuesFrom(<" + iriPrefix4Entities + "#R> <" + iriPrefix4Entities + "#H>))");
			axiomsExpected.add("SubClassOf(<" + iriPrefix4Entities + "#E> ObjectSomeValuesFrom(<" + iriPrefix4Entities + "#R> <" + iriPrefix4Entities + "#F>))");
			assertTrue(Utility.compareCollections(axiomsActual, axiomsExpected));
				
			Set<String> queriesActual = new HashSet<String>();
			for (QueryRecord queryRecord : pagoda.getQueryRecords())
				queriesActual.add(queryRecord.getQueryText());
			Set<String> queriesExpected = new HashSet<String>();
			queriesExpected.add("select ?x where { ?x <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Nothing> }");
			queriesExpected.add("select ?z where { <http://www.cs.ox.ac.uk/MORe#instantiation" + pagoda.indManager.index4Class.get(c).toString() + "> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> ?z }");
			queriesExpected.add("select ?z where { <http://www.cs.ox.ac.uk/MORe#instantiation" + pagoda.indManager.index4Class.get(d).toString() + "> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> ?z }");
			queriesExpected.add("select ?z where { <http://www.cs.ox.ac.uk/MORe#instantiation" + pagoda.indManager.index4Class.get(i).toString() + "> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> ?z }");
			assertTrue(Utility.compareCollections(queriesActual, queriesExpected));
			
			Set<OWLClass> gapClassesActual = new HashSet<OWLClass>();
			for (OWLClass c : pagoda.classesWithGap)
				gapClassesActual.add(c);
			Set<OWLClass> gapClassesExpected = new HashSet<OWLClass>();
			gapClassesExpected.add(c);
			gapClassesExpected.add(d);
			gapClassesExpected.add(i);
			assertTrue(Utility.compareCollections(gapClassesActual, gapClassesExpected));
			
			Set<OWLClass> unsatClassesActual = new HashSet<OWLClass>();
			for (OWLClass c : pagoda.unsatisfiableClasses)
				unsatClassesActual.add(c);
			Set<OWLClass> unsatClassesExpected = new HashSet<OWLClass>();
			unsatClassesExpected.add(a);
			assertTrue(Utility.compareCollections(unsatClassesActual, unsatClassesExpected));
			
			Set<String> finalUpperClausesActual = new HashSet<String>();
			for (DLClause cls : pagoda.program.getUpper().getClauses())
				finalUpperClausesActual.add(cls.toString());
			for (DLClause cls : pagoda.program.getUpper().getAuxiliaryClauses())
				finalUpperClausesActual.add(cls.toString());
			Set<String> finalUpperClausesExpected = new HashSet<String>();
			finalUpperClausesExpected.add("<" + iriPrefix4Entities + "#R_directed>(X,<http://www.cs.ox.ac.uk/PAGOdA/skolemised#individual0>) :- <" + iriPrefix4Entities + "#E>(X)");
			finalUpperClausesExpected.add("<" + iriPrefix4Entities + "#R>(X,Y) :- <" + iriPrefix4Entities + "#R_directed>(X,Y)");
			finalUpperClausesExpected.add("owl:Nothing(X) :- <" + iriPrefix4Entities + "#R_directed>(X,Y), owl:Nothing(Y)");
			finalUpperClausesExpected.add("owl:Nothing(X) :- <" + iriPrefix4Entities + "#G>(X), <" + iriPrefix4Entities + "#H>(X)");
			finalUpperClausesExpected.add("<" + iriPrefix4Entities + "#E>(X) :- <" + iriPrefix4Entities + "#D>(X)");
			finalUpperClausesExpected.add("<" + iriPrefix4Entities + "#J>(X) :- <" + iriPrefix4Entities + "#I>(X)");
			finalUpperClausesExpected.add("<" + iriPrefix4Entities + "#K>(X) :- <" + iriPrefix4Entities + "#I>(X)");
			finalUpperClausesExpected.add("<" + iriPrefix4Entities + "#G>(Y) :- <" + iriPrefix4Entities + "#C>(X), <" + iriPrefix4Entities + "#R>(X,Y)");
			finalUpperClausesExpected.add("<" + iriPrefix4Entities + "#H>(Y) :- <" + iriPrefix4Entities + "#D>(X), <" + iriPrefix4Entities + "#R>(X,Y)");
			finalUpperClausesExpected.add("<" + iriPrefix4Entities + "#E>(X) :- <" + iriPrefix4Entities + "#C>(X)");
			finalUpperClausesExpected.add("owl:Nothing(X) :- X != X");
			assertTrue(Utility.compareCollections(finalUpperClausesActual, finalUpperClausesExpected));
				
				
		}

		@Test
		public void nonLazyMaterialisationTest() throws Exception{
			setUp();
			OWLAxiom ax3 = factory.getOWLSubClassOfAxiom(c, e);
			OWLAxiom ax4 = factory.getOWLSubClassOfAxiom(d, e);
			OWLAxiom ax5 = factory.getOWLSubClassOfAxiom(e, factory.getOWLObjectSomeValuesFrom(r, f));
			OWLAxiom ax6 = factory.getOWLSubClassOfAxiom(c, factory.getOWLObjectAllValuesFrom(r, g));
			OWLAxiom ax7 = factory.getOWLSubClassOfAxiom(d, factory.getOWLObjectAllValuesFrom(r, h));
			OWLAxiom ax8 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectSomeValuesFrom(r, factory.getOWLObjectIntersectionOf(g,h)), i);
			
			OWLOntology o = manager.createOntology(IRI.create(iri));
			TestUtility.addAxiomsToOntology(o, manager, ax3, ax4, ax5, ax6, ax7, ax8);
			TestUtility.addDeclarationAxiomsToOntology(o, manager, c, d, e, f, g, h, i, r);
			
			manager.setOntologyDocumentIRI(o, IRI.create(iri));
			manager.saveOntology(o);
			
			Set<OWLClass> classesToClassify = new HashSet<OWLClass>();
			classesToClassify.add(c);
			classesToClassify.add(d);
			classesToClassify.add(e);
			classesToClassify.add(f);
			classesToClassify.add(g);
			classesToClassify.add(h);

			Logger_MORe.setLevel(Level.OFF);
			PAGOdAClassificationManager pagoda = new PAGOdAClassificationManager(o, classesToClassify);
			
			Set<String> axiomsActual= new HashSet<String>();
			for (OWLAxiom ax : pagoda.classify().getAxioms()){
				axiomsActual.add(ax.toString());
//				System.out.println(ax.toString());
			}
			Set<String> axiomsExpected = new HashSet<String>();
			axiomsExpected.add("SubClassOf(<" + iriPrefix4Entities + "#C> <" + iriPrefix4Entities + "#E>)");
			axiomsExpected.add("SubClassOf(<" + iriPrefix4Entities + "#C> ObjectAllValuesFrom(<" + iriPrefix4Entities + "#R> <" + iriPrefix4Entities + "#G>))");
			axiomsExpected.add("SubClassOf(ObjectIntersectionOf(<" + iriPrefix4Entities + "#G> <" + iriPrefix4Entities + "#H>) <internal:def#0>)");
			axiomsExpected.add("SubClassOf(<" + iriPrefix4Entities + "#D> <" + iriPrefix4Entities + "#E>)");
			axiomsExpected.add("SubClassOf(<" + iriPrefix4Entities + "#D> ObjectAllValuesFrom(<" + iriPrefix4Entities + "#R> <" + iriPrefix4Entities + "#H>))");
			axiomsExpected.add("SubClassOf(<" + iriPrefix4Entities + "#E> ObjectSomeValuesFrom(<" + iriPrefix4Entities + "#R> <" + iriPrefix4Entities + "#F>))");
			axiomsExpected.add("SubClassOf(ObjectSomeValuesFrom(<" + iriPrefix4Entities + "#R> <internal:def#0>) <" + iriPrefix4Entities + "#I>)");
			assertTrue(Utility.compareCollections(axiomsActual, axiomsExpected));
				
			Set<String> queriesActual = new HashSet<String>();
			for (QueryRecord queryRecord : pagoda.getQueryRecords()){
				queriesActual.add(queryRecord.getQueryText());
//				System.out.println(queryRecord.getQueryText());
			}
			Set<String> queriesExpected = new HashSet<String>();
			queriesExpected.add("select ?z where { <http://www.cs.ox.ac.uk/MORe#instantiation5> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> ?z }");
			queriesExpected.add("select ?z where { <http://www.cs.ox.ac.uk/MORe#instantiation4> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> ?z }");
			queriesExpected.add("select ?z where { <http://www.cs.ox.ac.uk/MORe#instantiation3> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> ?z }");
			assertTrue(Utility.compareCollections(queriesActual, queriesExpected));
			
			Set<OWLClass> gapClassesActual = new HashSet<OWLClass>();
			for (OWLClass c : pagoda.classesWithGap)
				gapClassesActual.add(c);
			Set<OWLClass> gapClassesExpected = new HashSet<OWLClass>();
			gapClassesExpected.add(c);
			gapClassesExpected.add(d);
			gapClassesExpected.add(e);
			assertTrue(Utility.compareCollections(gapClassesActual, gapClassesExpected));
			
			Set<OWLClass> unsatClassesActual = new HashSet<OWLClass>();
			for (OWLClass c : pagoda.unsatisfiableClasses)
				unsatClassesActual.add(c);
			Set<OWLClass> unsatClassesExpected = new HashSet<OWLClass>();
			assertTrue(Utility.compareCollections(unsatClassesActual, unsatClassesExpected));
			
			Set<String> finalUpperClausesActual = new HashSet<String>();
			for (DLClause cls : pagoda.program.getUpper().getClauses()){
				finalUpperClausesActual.add(cls.toString());
//				System.out.println(cls.toString());
			}
			Set<String> finalUpperClausesExpected = new HashSet<String>();
			finalUpperClausesExpected.add("<" + iriPrefix4Entities + "#R_directed>(X,<http://www.cs.ox.ac.uk/PAGOdA/skolemised#individual0>) :- <" + iriPrefix4Entities + "#E>(X)");
			finalUpperClausesExpected.add("<" + iriPrefix4Entities + "#E>(X) :- <" + iriPrefix4Entities + "#D>(X)");
			finalUpperClausesExpected.add("<" + iriPrefix4Entities + "#G>(Y) :- <" + iriPrefix4Entities + "#C>(X), <" + iriPrefix4Entities + "#R>(X,Y)");
			finalUpperClausesExpected.add("<" + iriPrefix4Entities + "#H>(Y) :- <" + iriPrefix4Entities + "#D>(X), <" + iriPrefix4Entities + "#R>(X,Y)");
			finalUpperClausesExpected.add("<" + iriPrefix4Entities + "#I>(X) :- <" + iriPrefix4Entities + "#R>(X,Y), <internal:def#0>(Y)");
			finalUpperClausesExpected.add("<internal:def#0>(X) :- <" + iriPrefix4Entities + "#G>(X), <" + iriPrefix4Entities + "#H>(X)");
			finalUpperClausesExpected.add("<" + iriPrefix4Entities + "#E>(X) :- <" + iriPrefix4Entities + "#C>(X)");
			finalUpperClausesExpected.add("owl:Nothing(X) :- X != X");
			assertTrue(Utility.compareCollections(finalUpperClausesActual, finalUpperClausesExpected));
				
				
		}	
		
		@Test
		public void additionOfSkolemConstantsToLowerStoreTest() throws Exception{
			Logger_MORe.setLevel(Level.OFF);
			
			setUp();
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(r, b));
			OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectSomeValuesFrom(r, b), c);
			
			OWLOntology o = manager.createOntology(IRI.create(iri));
			TestUtility.addAxiomsToOntology(o, manager, ax1, ax2);
			TestUtility.addDeclarationAxiomsToOntology(o, manager, a, b, c, r);
			
			manager.setOntologyDocumentIRI(o, IRI.create(iri));
			manager.saveOntology(o);
			
			Set<OWLClass> classesToClassify = new HashSet<OWLClass>();
			classesToClassify.add(a);

			PAGOdAClassificationManager pagoda = new PAGOdAClassificationManager(o, classesToClassify);
			pagoda.classify();
			
			Set<OWLClass> superClassesActual = new HashSet<OWLClass>();
			for (OWLClass c : pagoda.getAllSuperClasses(a)){
				superClassesActual.add(c);
//				System.out.println(c.toString());
			}
			Set<OWLClass> superClassesExpected = new HashSet<OWLClass>();
			superClassesExpected.add(c);
			superClassesExpected.add(factory.getOWLThing());
			assertTrue(Utility.compareCollections(superClassesActual, superClassesExpected));
		}	
		
		
		
		@Test
		public void additionOfSkolemConstantsToUpperStoreTest() throws Exception{
			Logger_MORe.setLevel(Level.OFF);
			
			setUp();
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(r, b));
			OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectAllValuesFrom(r, c));
			OWLAxiom ax3 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectIntersectionOf(b, c), d);
			OWLAxiom ax4 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectSomeValuesFrom(r, d), e);
			
			OWLOntology o = manager.createOntology(IRI.create(iri));
			TestUtility.addAxiomsToOntology(o, manager, ax1, ax2, ax3, ax4);
			TestUtility.addDeclarationAxiomsToOntology(o, manager, a, b, c, d, e, r);
			
			manager.setOntologyDocumentIRI(o, IRI.create(iri));
			manager.saveOntology(o);
			
			Set<OWLClass> classesToClassify = new HashSet<OWLClass>();
			classesToClassify.add(a);

			PAGOdAClassificationManager pagoda = new PAGOdAClassificationManager(o, classesToClassify, false);
			pagoda.classify();
			
			Set<OWLClass> potSuperClassesActual = new HashSet<OWLClass>();
			for (OWLClass c : pagoda.getPotentialSuperClasses(a)){
				potSuperClassesActual.add(c);
//				System.out.println(c.toString());
			}
			Set<OWLClass> potSuperClassesExpected = new HashSet<OWLClass>();
			potSuperClassesExpected.add(e);
			assertTrue(Utility.compareCollections(potSuperClassesActual, potSuperClassesExpected));
			
		}	
		
		@Test
		public void additionOfSkolemConstantsToUpperStoreTest2() throws Exception{//with multistage
			Logger_MORe.setLevel(Level.OFF);
			
			setUp();
			OWLAxiom ax1 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectSomeValuesFrom(r, b));
			OWLAxiom ax2 = factory.getOWLSubClassOfAxiom(a, factory.getOWLObjectAllValuesFrom(r, c));
			OWLAxiom ax3 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectIntersectionOf(b, c), factory.getOWLObjectUnionOf(d,e));
			OWLAxiom ax4 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectSomeValuesFrom(r, d), f);
			OWLAxiom ax5 = factory.getOWLSubClassOfAxiom(factory.getOWLObjectSomeValuesFrom(r, e), f);
			
			OWLOntology o = manager.createOntology(IRI.create(iri));
			TestUtility.addAxiomsToOntology(o, manager, ax1, ax2, ax3, ax4, ax5);
			TestUtility.addDeclarationAxiomsToOntology(o, manager, a, b, c, d, e, f, r);
			
			manager.setOntologyDocumentIRI(o, IRI.create(iri));
			manager.saveOntology(o);
			
			Set<OWLClass> classesToClassify = new HashSet<OWLClass>();
			classesToClassify.add(a);

			PAGOdAClassificationManager pagoda = new PAGOdAClassificationManager(o, classesToClassify, true);
			pagoda.classify();
			
			Set<OWLClass> potSuperClassesActual = new HashSet<OWLClass>();
			for (OWLClass c : pagoda.getPotentialSuperClasses(a)){
				potSuperClassesActual.add(c);
//				System.out.println(c.toString());
			}
			Set<OWLClass> potSuperClassesExpected = new HashSet<OWLClass>();
			potSuperClassesExpected.add(f);
			assertTrue(Utility.compareCollections(potSuperClassesActual, potSuperClassesExpected));
			
		}	

	}
