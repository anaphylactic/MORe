package util;


import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.junit.Assert;
import org.semanticweb.more.reasoner.MOReReasoner;
import org.semanticweb.more.util.Utility;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.OWLReasoner;


public class TestUtility {

	
	public static void addAxiomsToOntology(OWLOntology o, OWLOntologyManager manager, OWLAxiom... axioms){
		for (OWLAxiom ax : axioms)
			manager.addAxiom(o, ax);
	}
	public static void addDeclarationAxiomsToOntology(OWLOntology o, OWLOntologyManager manager, OWLEntity... ents){
		OWLDataFactory factory = manager.getOWLDataFactory(); 
		for (OWLEntity e : ents)
			manager.addAxiom(o, factory.getOWLDeclarationAxiom(e));
	}

	public static void checkEqualSets(Set<String> actual, Set<String> control){
		Set<String> diff1 = new HashSet<String>(actual);
		diff1.removeAll(control);
		Set<String> diff2 = new HashSet<String>(control);
		diff2.removeAll(actual);
		
		Assert.assertTrue(diff1.isEmpty());
		Assert.assertTrue(diff2.isEmpty());
	}
	
	
	public static boolean compareClassification(Collection<OWLClass> classes, OWLReasoner r1, OWLReasoner r2){
		Set<OWLClass> unsatClasses = r1.getUnsatisfiableClasses().getEntities();
		Set<OWLClass> unsatClasses2 = r2.getUnsatisfiableClasses().getEntities();
		boolean problem = false;
		for (OWLClass c : unsatClasses)
			if (!unsatClasses2.contains(c)){
				System.out.println(c.toString() + " lost unsat class");
				problem = true;
			}
		for (OWLClass c : unsatClasses2){
			if (!Utility.isInternalPredicate(c.toString()) && !unsatClasses.contains(c)){
				System.out.println(c.toString() + " extra unsat class");
				problem = true;
			}
		}

		if (!problem){
			for (OWLClass c : classes){
				if (!unsatClasses.contains(c)){
					Set<OWLClass> superclasses = r1.getSuperClasses(c, false).getFlattened();
					Set<OWLClass> superclasses2 = r2.getSuperClasses(c, false).getFlattened();
					Set<OWLClass> equivclasses = r1.getEquivalentClasses(c).getEntities();
					Set<OWLClass> equivclasses2 = r2.getEquivalentClasses(c).getEntities();

					for (OWLClass sup : superclasses){
						if (!superclasses2.contains(sup)){
							System.out.println(sup.toString() + " lost superclass of " + c.toString() );
							System.out.println(superclasses.toString());
							System.out.println(superclasses2.toString());
							problem = true;
						}
					}
					for (OWLClass sup : superclasses2){
						if (!Utility.isInternalPredicate(sup.toString()) && !superclasses.contains(sup)){
							System.out.println(sup.toString() + " extra superclass of " + c.toString());
							problem = true;
						}
					}

					for (OWLClass eq : equivclasses){
						if (!equivclasses2.contains(eq)){
							System.out.println(eq.toString() + " lost equivalent to  " + c.toString());
							problem = true;
						}
					}
					for (OWLClass eq : equivclasses2){
						if (!equivclasses.contains(eq)){
							System.out.println(eq.toString() + " extra equivalent to " + c.toString());
							problem = true;
						}
					}					
				}
			}
		}
		System.out.println("DONE!");
		return !problem;
	}
	
	public static boolean compareClassificationMORe(Collection<OWLClass> classes, OWLReasoner r, MOReReasoner more){
		Set<OWLClass> unsatClasses = r.getUnsatisfiableClasses().getEntities();
		Set<OWLClass> unsatClassesMORe = more.getAllUnsatisfiableClasses();
		boolean problem = false;
		for (OWLClass c : unsatClasses)
			if (!unsatClassesMORe.contains(c)){
				System.out.println(c.toString() + " lost unsat class");
				problem = true;
			}
		for (OWLClass c : unsatClassesMORe){
			if (!Utility.isInternalPredicate(c.toString()) && !unsatClasses.contains(c)){
				System.out.println(c.toString() + " extra unsat class");
				problem = true;
			}
		}

		if (!problem){
			for (OWLClass c : classes){
				if (!unsatClasses.contains(c) && c.toString().contains("http://www.w3.org/TR/2003/PR-owl-guide-20031209/wine#PinotBlanc")){
					Set<OWLClass> superclasses = r.getSuperClasses(c, false).getFlattened();
					superclasses.addAll(r.getEquivalentClasses(c).getEntities());
					superclasses.remove(c);
					Set<OWLClass> superclassesMORe = more.getAllSuperClasses(c);

					for (OWLClass sup : superclasses){
//						if (!superclassesMORe.contains(sup)){
						if (! superclassesMORe.isEmpty() && !superclassesMORe.contains(sup)){
							System.out.println(sup.toString() + " lost superclass of " + c.toString() );
							System.out.println(superclasses.toString());
							System.out.println(superclassesMORe.toString());
							problem = true;
						}
					}
					for (OWLClass sup : superclassesMORe){
						if (!Utility.isInternalPredicate(sup.toString()) && !superclasses.contains(sup)){
							System.out.println(sup.toString() + " extra superclass of " + c.toString());
							problem = true;
						}
					}
				}
			}
		}
		System.out.println("DONE!");
		return !problem;
	}
	
}
