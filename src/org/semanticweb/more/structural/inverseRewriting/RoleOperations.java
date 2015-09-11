package org.semanticweb.more.structural.inverseRewriting;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLIndividualAxiom;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectMaxCardinality;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLPropertyAxiom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;

public class RoleOperations {
	protected final static OWLDataFactory m_factory=new OWLDataFactoryImpl();
	protected Set<String> rewrittenRoles = new HashSet<String>();
	
	protected static Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> getRoleHierarchy(Set<OWLAxiom> axioms){
		Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> roleHierarchy = 
				new HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>>();
		for (OWLAxiom axiom : axioms)
			if (axiom instanceof OWLSubObjectPropertyOfAxiom) {
				OWLObjectPropertyExpression subP = ((OWLSubObjectPropertyOfAxiom) axiom).getSubProperty().getSimplified();
				OWLObjectPropertyExpression superP = ((OWLSubObjectPropertyOfAxiom) axiom).getSuperProperty().getSimplified();

				if (roleHierarchy.containsKey(subP)){//then it must also contain inv(subP) as a key because we add both at the same time
					roleHierarchy.get(subP).add(superP);
					roleHierarchy.get(subP.getInverseProperty().getSimplified()).add(superP.getInverseProperty().getSimplified());
				}
				else{
					Set<OWLObjectPropertyExpression> superRoles = new HashSet<OWLObjectPropertyExpression>();
					superRoles.add(subP);//necessary??
					superRoles.add(superP);
					roleHierarchy.put(subP, superRoles);

					Set<OWLObjectPropertyExpression> superRolesInv = new HashSet<OWLObjectPropertyExpression>();
					superRolesInv.add(subP.getInverseProperty().getSimplified());//necessary??
					superRolesInv.add(superP.getInverseProperty().getSimplified());
					roleHierarchy.put(subP.getInverseProperty().getSimplified(), superRolesInv);
				}

			}

		boolean flag = true;
		while (flag) {
			flag = false;
			for (OWLObjectPropertyExpression p : roleHierarchy.keySet()) {
				Set<OWLObjectPropertyExpression> superRolesCopy = new HashSet<OWLObjectPropertyExpression>(roleHierarchy.get(p));
				for (OWLObjectPropertyExpression s : superRolesCopy)
					if (roleHierarchy.containsKey(s) && roleHierarchy.get(p).addAll(roleHierarchy.get(s))){
						flag = true;
					}
			}
		} 
		//		System.out.println("roleHierarchy: done");
		return roleHierarchy;
	}


	//	protected static Set<OWLObjectPropertyExpression> getGeneratingRoles(OWLOntology o){
	//
	//		Map<OWLObjectPropertyExpression, Set<OWLAxiom>> generatingRolesMap = getGeneratingRolesMap(o);
	//		Set<OWLObjectPropertyExpression> generatingRoles=generatingRolesMap.keySet();
	//		return generatingRoles;
	//	}


	public Set<String> getRewrittenRoles(){
		return rewrittenRoles;
	}


	protected OWLObjectPropertyExpression getNewRoleName(OWLObjectPropertyExpression role, Set<OWLObjectPropertyExpression> nonRW){
		OWLObjectPropertyExpression nrole; 
		if (role.isAnonymous()&&!nonRW.contains(role)) {
			String invname="Newgsd"+role.getInverseProperty().getSimplified().toString().substring(1, role.getInverseProperty().getSimplified().toString().length()-1);
			rewrittenRoles.add(invname);
			nrole=m_factory.getOWLObjectProperty(IRI.create(invname));
		}
		else nrole=role;
		return nrole;
	}


	protected static boolean isGenerating(OWLObjectPropertyExpression role, Set<OWLAxiom> axioms){
		Set<OWLObjectPropertyExpression> genRoles=getGeneratingRoles(axioms);
		return genRoles.contains(role);
	}


	protected static Set<OWLObjectPropertyExpression> getGeneratingRoles(Set<OWLAxiom> axioms){

		Map<OWLObjectPropertyExpression, Set<OWLAxiom>> generatingRolesMap = getGeneratingRolesMap(axioms);
		Set<OWLObjectPropertyExpression> generatingRoles=generatingRolesMap.keySet();
		return generatingRoles;
	}


	protected static Map<OWLObjectPropertyExpression, Set<OWLAxiom>> getGeneratingRolesMap(Set<OWLAxiom> axioms){

		Map<OWLObjectPropertyExpression, Set<OWLAxiom>> generatingRoles = new HashMap<OWLObjectPropertyExpression, Set<OWLAxiom>>();

		Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> roleHierarchy=getRoleHierarchy(axioms);

		for (OWLAxiom axiom : axioms)
			if (axiom instanceof OWLSubClassOfAxiom) {
				Set<OWLClassExpression> superclass = ((OWLSubClassOfAxiom) axiom).getSuperClass().asDisjunctSet();

				OWLObjectPropertyExpression p;
				for (OWLClassExpression disj:superclass) {
					if (disj instanceof OWLObjectMinCardinality){
						p = ((OWLObjectMinCardinality) disj).getProperty().getSimplified();
						Set<OWLAxiom> aux = generatingRoles.get(p);
						if (aux != null)
							aux.add(axiom);
						else{
							aux = new HashSet<OWLAxiom>();
							aux.add(axiom);
							generatingRoles.put(p, aux);
						}
					}
					else if (disj instanceof OWLObjectSomeValuesFrom){
						p = ((OWLObjectSomeValuesFrom) disj).getProperty().getSimplified();
						Set<OWLAxiom> aux = generatingRoles.get(p);
						if (aux != null)
							aux.add(axiom);
						else{
							aux = new HashSet<OWLAxiom>();
							aux.add(axiom);
							generatingRoles.put(p, aux);
						}
					} 
				}
			}
			else if (axiom instanceof OWLObjectPropertyAssertionAxiom){
				OWLObjectPropertyExpression p = ((OWLObjectPropertyAssertionAxiom) axiom).getProperty().getSimplified();
				Set<OWLAxiom> aux = generatingRoles.get(p);
				if (aux != null)
					aux.add(axiom);
				else{
					aux = new HashSet<OWLAxiom>();
					aux.add(axiom);
					generatingRoles.put(p, aux);
				}
			}
		boolean flag = true;
		while (flag){
			flag = false;
			Set<OWLObjectPropertyExpression> copyGeneratingRoles = new HashSet<OWLObjectPropertyExpression>(generatingRoles.keySet());
			for (OWLObjectPropertyExpression p : copyGeneratingRoles){

				Set<OWLObjectPropertyExpression> superRoles = roleHierarchy.get(p);

				if (superRoles != null)
					for (OWLObjectPropertyExpression q : superRoles){
						if (!generatingRoles.containsKey(q)){
							flag = true;
							Set<OWLAxiom> aux = new HashSet<OWLAxiom>();
							aux.addAll(generatingRoles.get(p));
							generatingRoles.put(q, aux);
						}
						else
							if (generatingRoles.get(q).addAll(generatingRoles.get(p))){
								flag = true;
							}
					}
			}
		}

		//		System.out.println("finding generatingRoles: done");
		//	System.out.println(generatingRoles.keySet().size() + " generating roles");
		return generatingRoles;
	}


	//	protected static Map<OWLObjectPropertyExpression, Set<OWLAxiom>> getGeneratingRolesMap(OWLOntology o){
	//		Set<OWLPropertyAxiom> axioms=o.getAxioms();
	//		return getGeneratingRolesMap(axioms);
	//	}




	protected static Set<OWLObjectPropertyExpression> getNonRewritableRoles(Set<OWLAxiom> axioms, boolean hasNominals) {
		Set<OWLObjectPropertyExpression> nonRewritableRoles = new HashSet<OWLObjectPropertyExpression>();
		Set<OWLObjectPropertyExpression> generatingRoles = getGeneratingRoles(axioms);
		Set<OWLObjectPropertyExpression> atMostRoles = getRolesInAtMost(axioms);
		Set<OWLObjectProperty> allRoles = new HashSet<OWLObjectProperty>();
		for (OWLAxiom axiom:axioms) allRoles.addAll(axiom.getObjectPropertiesInSignature()); 
		for (OWLObjectProperty property : allRoles) {
			if (generatingRoles.contains(property.getInverseProperty().getSimplified()) && atMostRoles.contains(property) && (hasNominals||generatingRoles.contains(property)))
				nonRewritableRoles.add(property.getInverseProperty());		
			if (generatingRoles.contains(property) && atMostRoles.contains(property.getInverseProperty())&& (hasNominals||generatingRoles.contains(property.getInverseProperty())))
				nonRewritableRoles.add(property.getInverseProperty());
		}
		return nonRewritableRoles;
	}


	//	protected static Set<OWLObjectPropertyExpression> getInverseRoles(Set<OWLAxiom> axioms) {
	//		Set<OWLObjectPropertyExpression> inverseRoles = new HashSet<OWLObjectPropertyExpression>();
	//		Set<OWLObjectProperty> allRoles = new HashSet<OWLObjectProperty>();
	//		for (OWLAxiom axiom:axioms) allRoles.addAll(axiom.getObjectPropertiesInSignature());
	//		for (OWLAxiom axiom:axioms) if axiom.
	//		for (OWLObjectProperty property : allRoles) {
	//			if Axiom.class
	//			property.getInverseProperty()) && atMostRoles.contains(property))
	//				|| (generatingRoles.contains(property) && atMostRoles.contains(property.getInverseProperty())))
	//				nonRewritableRoles.add(property.getInverseProperty());
	//		}
	//		return nonRewritableRoles;
	//	}


	public static boolean  isRewritable(OWLObjectPropertyExpression role, Set<OWLAxiom> axioms, boolean hasNom)
	{
		Set<OWLObjectPropertyExpression> nonRewritableRoles = getNonRewritableRoles(axioms, hasNom);
		return !nonRewritableRoles.contains(role);
	}



	//String invname="Newgsd"+role.getInverseProperty().getSimplified().toString().substring(1, role.getInverseProperty().getSimplified().toString().length()-2);

	public static OWLObjectPropertyExpression getOriginalRole(OWLObjectPropertyExpression role)
	{
		OWLObjectPropertyExpression orig;
		if (role.toString().contains("Newgsd")) orig=m_factory.getOWLObjectProperty(IRI.create(role.toString().replace("<","").replace(">","").substring(6))).getInverseProperty();
		else orig=role;
		return orig;
	}

	protected static Set<OWLObjectPropertyExpression> getRolesInAtMost(Set<OWLAxiom> axioms){
		//Set<OWLPropertyAxiom>
		Map<OWLObjectPropertyExpression, Set<OWLAxiom>> geRolesInAtMostMap =  getRolesInAtMostMap(axioms);
		Set<OWLObjectPropertyExpression> generatingRoles=geRolesInAtMostMap.keySet();
		return generatingRoles;
	}


	protected static boolean isActive(OWLObjectPropertyExpression role, Set<OWLAxiom> axioms){
		Set<OWLObjectPropertyExpression> activeRoles=getActiveRoles(axioms);
		return activeRoles.contains(role);
	}

	protected  static Set<OWLObjectPropertyExpression>  getActiveRoles(Set<OWLAxiom> axioms){

		Set<OWLObjectPropertyExpression> activeRoles = new HashSet<OWLObjectPropertyExpression>();
		Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> roleHierarchy=getRoleHierarchy(axioms);

		for (OWLAxiom axiom : axioms)
			if (axiom instanceof OWLSubClassOfAxiom) {

				OWLClassExpression superclass = ((OWLSubClassOfAxiom) axiom).getSuperClass();
				OWLClassExpression subclass = ((OWLSubClassOfAxiom) axiom).getSubClass();

				for (OWLClassExpression disjunct:superclass.asDisjunctSet()){
					if (disjunct instanceof OWLObjectMaxCardinality) 
						activeRoles.add(getOriginalRole(((OWLObjectMaxCardinality) disjunct).getProperty())); 
					if (disjunct instanceof OWLObjectAllValuesFrom) 
						activeRoles.add(getOriginalRole(((OWLObjectAllValuesFrom) disjunct).getProperty()));
				}


				for (OWLClassExpression conjunct:subclass.asConjunctSet()) 
					if (conjunct instanceof OWLObjectSomeValuesFrom) 
						activeRoles.add(getOriginalRole(((OWLObjectSomeValuesFrom) conjunct).getProperty())); 						
			}

		//not very efficient; mapping in the other direction?				
		for (OWLObjectPropertyExpression p : roleHierarchy.keySet())
			for (OWLObjectPropertyExpression q : roleHierarchy.get(p)) 
				if (activeRoles.contains(q)) activeRoles.add(p);


		//		System.out.println("finding roles in atMost restrictions: done");
		return activeRoles;
	}


	protected static Map<OWLObjectPropertyExpression, Set<OWLAxiom>> getRolesInAtMostMap(Set<OWLAxiom> axioms){

		Map<OWLObjectPropertyExpression, Set<OWLAxiom>> atMostRoles2Axiom = new HashMap<OWLObjectPropertyExpression, Set<OWLAxiom>>();
		//Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> roleHierarchy=getRoleHierarchy(axioms);

		for (OWLAxiom axiom : axioms)
			if (axiom instanceof OWLSubClassOfAxiom) {
				OWLClassExpression superclass = ((OWLSubClassOfAxiom) axiom).getSuperClass();
				OWLObjectPropertyExpression p;


				for (OWLClassExpression disjunct:superclass.asDisjunctSet())
					if (disjunct instanceof OWLObjectMaxCardinality)
					{ p = ((OWLObjectMaxCardinality) disjunct).getProperty().getSimplified();
					if (atMostRoles2Axiom.containsKey(p))
						atMostRoles2Axiom.get(p).add(axiom);
					else{
						Set<OWLAxiom> aux = new HashSet<OWLAxiom>();
						aux.add(axiom);
						atMostRoles2Axiom.put(p, aux);
					}
					}
			}
		//		System.out.println("finding roles in atMost restrictions: done");
		return atMostRoles2Axiom;
	}


	protected Map<OWLObjectPropertyExpression, Set<OWLAxiom>> getRolesInAtMostMap(OWLOntology o){
		return getRolesInAtMostMap(o.getAxioms());
	}

	public static Set<OWLPropertyAxiom> getPropertyAxioms(Set<OWLAxiom> axioms){
		Set<OWLPropertyAxiom> result=new HashSet<OWLPropertyAxiom>();
		for (OWLAxiom axiom:axioms)
			if (axiom.isOfType(AxiomType.RBoxAxiomTypes))
				result.add((OWLPropertyAxiom) axiom);
		return result;
	}

	public static Set<OWLIndividualAxiom> getAssertionAxioms(Set<OWLAxiom> axioms){
		Set<OWLIndividualAxiom> result=new HashSet<OWLIndividualAxiom>();
		for (OWLAxiom axiom:axioms)
			if (axiom.isOfType(AxiomType.ABoxAxiomTypes))
				result.add((OWLIndividualAxiom) axiom);
		return result;
	}




}
