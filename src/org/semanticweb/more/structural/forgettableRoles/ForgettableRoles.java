package org.semanticweb.more.structural.forgettableRoles;


import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLAnnotationAssertionAxiom;
import org.semanticweb.owlapi.model.OWLAnnotationPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLAnnotationPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLAsymmetricObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLAxiomVisitor;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLClassExpressionVisitor;
import org.semanticweb.owlapi.model.OWLDataAllValuesFrom;
import org.semanticweb.owlapi.model.OWLDataExactCardinality;
import org.semanticweb.owlapi.model.OWLDataHasValue;
import org.semanticweb.owlapi.model.OWLDataMaxCardinality;
import org.semanticweb.owlapi.model.OWLDataMinCardinality;
import org.semanticweb.owlapi.model.OWLDataPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLDataSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLDatatypeDefinitionAxiom;
import org.semanticweb.owlapi.model.OWLDeclarationAxiom;
import org.semanticweb.owlapi.model.OWLDifferentIndividualsAxiom;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointDataPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointUnionAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentDataPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLFunctionalDataPropertyAxiom;
import org.semanticweb.owlapi.model.OWLFunctionalObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLHasKeyAxiom;
import org.semanticweb.owlapi.model.OWLInverseFunctionalObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLInverseObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLIrreflexiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLNegativeDataPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLNegativeObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectExactCardinality;
import org.semanticweb.owlapi.model.OWLObjectHasSelf;
import org.semanticweb.owlapi.model.OWLObjectHasValue;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectMaxCardinality;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectOneOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLReflexiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLSameIndividualAxiom;
import org.semanticweb.owlapi.model.OWLSubAnnotationPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubDataPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom;
import org.semanticweb.owlapi.model.OWLSymmetricObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLTransitiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.SWRLRule;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;


public class ForgettableRoles {

	OWLOntology ontology;
	OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
	OWLDataFactoryImpl factory = new OWLDataFactoryImpl();

	Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> roleHierarchyUp = new HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>>();
	Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> roleHierarchyDown = new HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>>();
	Collection<OWLObjectPropertyExpression> generatingRoles = new HashSet<OWLObjectPropertyExpression>();
	Collection<OWLSubPropertyChainOfAxiom> complexRoleInclusions = new LinkedList<OWLSubPropertyChainOfAxiom>();
	//roles that are forgettable
	Collection<OWLObjectPropertyExpression> forgettableRoles;
	//roles that are not forgettable but only because of the domain
	Map<OWLObjectPropertyExpression, OWLClassExpression> onlyNotForgettableBecauseOfDomain;
	//roles that are not forgettable at all
	Set<OWLObjectPropertyExpression> notForgettable;
	Collection<OWLObjectPropertyExpression> rolesWithSomeNotForgettableSubproperty = new LinkedList<OWLObjectPropertyExpression>();
	
	Collection<OWLAxiom> rewrittenAxioms = new LinkedList<OWLAxiom>();
	int nExistentialRestrictionsRewrittenAway = 0;

	
	
	
	public Collection<OWLAxiom> rewrite(OWLOntology o) throws OWLOntologyCreationException{
		ontology = o;
		if (isTechniqueApplicable()){
			processRoles();
			rewriteAxioms();
		}
		else{
			Logger_MORe.logDebug("couldn't apply forgettable roles technique");
			return null;
		}
		return rewrittenAxioms;
	}

	protected boolean isTechniqueApplicable(){
		boolean ret = true;
		onlyNotForgettableBecauseOfDomain = new HashMap<OWLObjectPropertyExpression, OWLClassExpression>();
		notForgettable = new HashSet<OWLObjectPropertyExpression>();
		AxiomVisitor axiomVisitor = new AxiomVisitor();
		Iterator<OWLAxiom> iter = ontology.getAxioms().iterator();
		while(iter.hasNext() && ret)
			ret = !axiomVisitor.containsSomeFormOfNegation(iter.next());	
		return ret;
	}
	
	protected void processRoles(){
		computeTransitiveClosureOfRoleHierarchy();
		
		//init forgettableRoles
		forgettableRoles = new LinkedList<OWLObjectPropertyExpression>();
		for (OWLObjectProperty p : ontology.getObjectPropertiesInSignature()){
			forgettableRoles.add(p);
			forgettableRoles.add(p.getInverseProperty());
		}
		
		
		//maybe use the hierarchy to find all the roles that are generating
		//and remove from notforgettable all those which aren't
		
		completeNotForgettableRolesWithHierarchy();
		forgettableRoles.removeAll(notForgettable);
		for (OWLObjectPropertyExpression p : notForgettable)
			onlyNotForgettableBecauseOfDomain.remove(p);
		
		completeDomainMapWithRoleHierarchy();
		forgettableRoles.removeAll(onlyNotForgettableBecauseOfDomain.keySet());
		
		rolesWithSomeNotForgettableSubproperty.addAll(notForgettable);
		for (OWLObjectPropertyExpression p : forgettableRoles){
			Set<OWLObjectPropertyExpression> subRoles = roleHierarchyDown.get(p);
			if (subRoles != null){
				Iterator<OWLObjectPropertyExpression> iter = subRoles.iterator();
				boolean foundOne = false;
				while (!foundOne && iter.hasNext())
					foundOne = notForgettable.contains(iter.next());
				if (foundOne)
					rolesWithSomeNotForgettableSubproperty.add(p);				
			}
		}
		for (OWLObjectPropertyExpression p : onlyNotForgettableBecauseOfDomain.keySet()){
			boolean foundOne = false;
			Set<OWLObjectPropertyExpression> subRoles = roleHierarchyDown.get(p);
			if (subRoles != null){
				Iterator<OWLObjectPropertyExpression> iter = subRoles.iterator();
				while (!foundOne && iter.hasNext())
					foundOne = notForgettable.contains(iter.next());
				if (foundOne)
					rolesWithSomeNotForgettableSubproperty.add(p);
			}
		}
		
		Logger_MORe.logDebug(forgettableRoles.size() + " forgettable roles:");
		Logger_MORe.logDebug(onlyNotForgettableBecauseOfDomain.keySet().size() + " roles only not forgettable because of domain or range axioms:");
		Logger_MORe.logDebug(notForgettable.size() + " not forgettable roles:");

		Logger_MORe.logDebug(ontology.getObjectPropertiesInSignature().size()*2 + " total roles (counting inverses as well)");
		
	}
	protected void completeNotForgettableRolesWithHierarchy() {
		//every subrole or member of a subrole chain of a role that is not forgettable is not forgettable either
		Set<OWLObjectPropertyExpression> newNotForgettableRolesFound = new HashSet<OWLObjectPropertyExpression>(notForgettable);
		while (!newNotForgettableRolesFound.isEmpty()){
			HashSet<OWLObjectPropertyExpression> newNewNotForgettableRolesFound = new HashSet<OWLObjectPropertyExpression>();
			for (OWLSubPropertyChainOfAxiom ax : complexRoleInclusions){
				OWLObjectPropertyExpression p = ax.getSuperProperty().getSimplified();
				if (newNotForgettableRolesFound.contains(p))
					for(OWLObjectPropertyExpression q : ax.getPropertyChain())
						newNewNotForgettableRolesFound.add(q.getSimplified());
				if (newNotForgettableRolesFound.contains(p.getInverseProperty().getSimplified()))
					for(OWLObjectPropertyExpression q : ax.getPropertyChain())
						newNewNotForgettableRolesFound.add(q.getInverseProperty().getSimplified());
			}
			newNewNotForgettableRolesFound.removeAll(notForgettable);
			if (!newNewNotForgettableRolesFound.isEmpty())
				notForgettable.addAll(newNewNotForgettableRolesFound);
			newNotForgettableRolesFound = newNewNotForgettableRolesFound;
		}
		newNotForgettableRolesFound = new HashSet<OWLObjectPropertyExpression>();
		for (OWLObjectPropertyExpression p : notForgettable){//looping once is enough because roleHierarchyDown is closed under transitivity
			Set<OWLObjectPropertyExpression> subRoles = roleHierarchyDown.get(p);
			if (subRoles != null)
				newNotForgettableRolesFound.addAll(subRoles);
		}
		notForgettable.addAll(newNotForgettableRolesFound);
	}
	protected void computeTransitiveClosureOfRoleHierarchy(){
		boolean flag = true;
		while (flag) {
			flag = false;
			for (Entry<OWLObjectPropertyExpression,Set<OWLObjectPropertyExpression>> entry : roleHierarchyUp.entrySet()) {
				Set<OWLObjectPropertyExpression> superRolesCopy = new HashSet<OWLObjectPropertyExpression>(entry.getValue());
				for (OWLObjectPropertyExpression s : superRolesCopy){
					Set<OWLObjectPropertyExpression> moreSuperRoles = roleHierarchyUp.get(s);
					if (moreSuperRoles != null && entry.getValue().addAll(moreSuperRoles))
						flag = true;
				}
			}
		}
		flag = true;
		while (flag) {
			flag = false;
			for (Entry<OWLObjectPropertyExpression,Set<OWLObjectPropertyExpression>> entry : roleHierarchyDown.entrySet()) {
				Set<OWLObjectPropertyExpression> subRolesCopy = new HashSet<OWLObjectPropertyExpression>(entry.getValue());
				for (OWLObjectPropertyExpression s : subRolesCopy){
					Set<OWLObjectPropertyExpression> moreSubRoles = roleHierarchyDown.get(s);
					if (moreSubRoles != null && entry.getValue().addAll(moreSubRoles))
						flag = true;
				}
			}
		}
	}
	protected void completeDomainMapWithRoleHierarchy() {//we also need to consider here properties that didn't have a domain axiom of their own but are subproperties of these
		//we need to have already computed the transitive closure of the role hierarchy at this point
		Set<Entry<OWLObjectPropertyExpression, OWLClassExpression>> entriesCopy = new HashSet<Map.Entry<OWLObjectPropertyExpression,OWLClassExpression>>(onlyNotForgettableBecauseOfDomain.entrySet());//better make a copy since we are going to add new entries inside the for loop
		for (Entry<OWLObjectPropertyExpression, OWLClassExpression> entry : entriesCopy){
			OWLObjectPropertyExpression p = entry.getKey();
			Set<OWLObjectPropertyExpression> subProperties = roleHierarchyDown.get(p);
			if (subProperties != null)
				for (OWLObjectPropertyExpression q : subProperties){
					if (!p.equals(q)){
						OWLClassExpression domain = onlyNotForgettableBecauseOfDomain.get(q);
						if (domain == null)
							onlyNotForgettableBecauseOfDomain.put(q, entry.getValue());
					}
				}
		}
		
		for (Entry<OWLObjectPropertyExpression, OWLClassExpression> entry : onlyNotForgettableBecauseOfDomain.entrySet()){
			OWLObjectPropertyExpression p = entry.getKey();
			Set<OWLObjectPropertyExpression> superProperties = roleHierarchyUp.get(p);
			if (superProperties != null)
				for (OWLObjectPropertyExpression q : superProperties){
					if (!p.equals(q)){
						OWLClassExpression domain = onlyNotForgettableBecauseOfDomain.get(q);
						if (domain != null)
							entry.setValue(getIntersectionOfClassExpressions(domain, entry.getValue()));
					}
				}
		}
	}
	
	protected void rewriteAxioms(){	
		AxiomRewriter rewriter = new AxiomRewriter();
		for (OWLAxiom ax : ontology.getAxioms())
			rewrittenAxioms.addAll(rewriter.getRewrittenAxiom(ax));
	}
	
	protected OWLClassExpression getIntersectionOfClassExpressions(OWLClassExpression e1, OWLClassExpression e2){
		Set<OWLClassExpression> exps = new HashSet<OWLClassExpression>();
		if (e1 instanceof OWLObjectIntersectionOf)
			exps.addAll(((OWLObjectIntersectionOf) e1).getOperands());
		else
			exps.add(e1);
		if (e2 instanceof OWLObjectIntersectionOf)
			exps.addAll(((OWLObjectIntersectionOf) e2).getOperands());
		else
			exps.add(e2);
		if (exps.size() == 1)
			return exps.iterator().next();
		return factory.getOWLObjectIntersectionOf(exps);
	}
	
	class AxiomVisitor implements OWLAxiomVisitor{

		protected boolean containsSomeFormOfNegation = false; 
		protected ClassVisitor classVisitor = new ClassVisitor();

		public boolean containsSomeFormOfNegation(OWLAxiom ax){
			containsSomeFormOfNegation = false;
			ax.accept(this);
			if (containsSomeFormOfNegation)
				Logger_MORe.logDebug(ax.toString());
			return containsSomeFormOfNegation;
		}

		private void registerPropertyInclusion(OWLObjectPropertyExpression subP, OWLObjectPropertyExpression superP){
			subP = subP.getSimplified();
			superP = superP.getSimplified();

			Set<OWLObjectPropertyExpression> superProperties = roleHierarchyUp.get(subP); 
			if (superProperties != null){//then it must also contain inv(subP) as a key because we add both at the same time
				superProperties.add(superP);
				roleHierarchyUp.get(subP.getInverseProperty().getSimplified()).add(superP.getInverseProperty().getSimplified());
			}
			else{
				superProperties = new HashSet<OWLObjectPropertyExpression>();
				superProperties.add(subP);//necessary??
				superProperties.add(superP);
				roleHierarchyUp.put(subP, superProperties);

				Set<OWLObjectPropertyExpression> superPropertiesInv = new HashSet<OWLObjectPropertyExpression>();
				superPropertiesInv.add(subP.getInverseProperty().getSimplified());//necessary??
				superPropertiesInv.add(superP.getInverseProperty().getSimplified());
				roleHierarchyUp.put(subP.getInverseProperty().getSimplified(), superPropertiesInv);
			}
			Set<OWLObjectPropertyExpression> subProperties = roleHierarchyDown.get(superP); 
			if (subProperties != null){//then it must also contain inv(subP) as a key because we add both at the same time
				subProperties.add(subP);
				roleHierarchyDown.get(superP.getInverseProperty().getSimplified()).add(subP.getInverseProperty().getSimplified());
			}
			else{
				subProperties = new HashSet<OWLObjectPropertyExpression>();
				subProperties.add(superP);//necessary??
				subProperties.add(subP);
				roleHierarchyDown.put(superP, subProperties);

				Set<OWLObjectPropertyExpression> subPropertiesInv = new HashSet<OWLObjectPropertyExpression>();
				subPropertiesInv.add(superP.getInverseProperty().getSimplified());//necessary??
				subPropertiesInv.add(subP.getInverseProperty().getSimplified());
				roleHierarchyDown.put(superP.getInverseProperty().getSimplified(), subPropertiesInv);
			}
		}

		private void registerDomainAxiom(OWLObjectPropertyExpression p, OWLClassExpression domain){
			containsSomeFormOfNegation = classVisitor.containsSomeFormOfNegation(domain, true);
			if (!containsSomeFormOfNegation){
				OWLClassExpression currentDomain = onlyNotForgettableBecauseOfDomain.get(p);
				if (currentDomain != null){
					domain = getIntersectionOfClassExpressions(currentDomain, domain);
					Logger_MORe.logDebug("several domains for role " + p.toString() + ": " + domain.toString());
				}					
				onlyNotForgettableBecauseOfDomain.put(p, domain);
			}
		}

		@Override
		public void visit(OWLSubClassOfAxiom arg0) {
			OWLClassExpression subclass = arg0.getSubClass();
			OWLClassExpression superclass = ((OWLSubClassOfAxiom) arg0).getSuperClass();

			if (subclass instanceof OWLObjectSomeValuesFrom && ((OWLObjectSomeValuesFrom) subclass).getFiller().isOWLThing()){//is DomainAxiom
				OWLObjectPropertyExpression p = ((OWLObjectSomeValuesFrom) subclass).getProperty().getSimplified();
				registerDomainAxiom(p, superclass);
			}
			else if (subclass.isOWLThing() && superclass instanceof OWLObjectAllValuesFrom){//is also DomainAxiom
				OWLObjectPropertyExpression p = ((OWLObjectAllValuesFrom) superclass).getProperty().getInverseProperty().getSimplified();
				OWLClassExpression filler = ((OWLObjectAllValuesFrom) superclass).getFiller();
				registerDomainAxiom(p, filler);
			}
			else{
				if (classVisitor.containsSomeFormOfNegation(subclass, false)){
					containsSomeFormOfNegation = true;
					return;
				}
				containsSomeFormOfNegation = classVisitor.containsSomeFormOfNegation(superclass, true);
			}
		}

		@Override
		public void visit(OWLEquivalentClassesAxiom arg0) {
			boolean aux = false;
			if (arg0.getClassExpressions().size()>1) {
				Iterator<OWLClassExpression> iterator = arg0.getClassExpressions().iterator();
				OWLClassExpression first=iterator.next();
				OWLClassExpression last=first;
				while (iterator.hasNext() && !aux) {
					OWLClassExpression next=iterator.next();
					aux = containsSomeFormOfNegation(factory.getOWLSubClassOfAxiom(last, next));
					last=next;
				}
				if (!aux)
					aux = containsSomeFormOfNegation(factory.getOWLSubClassOfAxiom(last, first));
			}
			containsSomeFormOfNegation = aux;
		}

		@Override
		public void visit(OWLObjectPropertyDomainAxiom arg0) {
			registerDomainAxiom(arg0.getProperty(), arg0.getDomain());
		}

		@Override
		public void visit(OWLObjectPropertyRangeAxiom arg0) {
			registerDomainAxiom(arg0.getProperty().getInverseProperty(), arg0.getRange());
		}

		@Override
		public void visit(OWLSubObjectPropertyOfAxiom arg0) {
			registerPropertyInclusion(arg0.getSubProperty(), arg0.getSuperProperty());
		}

		@Override
		public void visit(OWLEquivalentObjectPropertiesAxiom arg0) {
			Set<OWLObjectPropertyExpression> objectPropertyExpressions = arg0.getProperties();
			if (objectPropertyExpressions.size()>1) {
				Iterator<OWLObjectPropertyExpression> iterator=objectPropertyExpressions.iterator();
				OWLObjectPropertyExpression first=iterator.next();
				OWLObjectPropertyExpression last=first;
				while (iterator.hasNext()) {
					OWLObjectPropertyExpression next=iterator.next();
					registerPropertyInclusion(last, next);
					last=next;
				}
				registerPropertyInclusion(last, first);
			}
		}

		@Override
		public void visit(OWLSubPropertyChainOfAxiom arg0) {
			complexRoleInclusions.add(arg0);
		}

		@Override
		public void visit(OWLInverseObjectPropertiesAxiom arg0) {
			OWLObjectPropertyExpression p1 = arg0.getFirstProperty();
			OWLObjectPropertyExpression p2 = arg0.getSecondProperty();
			registerPropertyInclusion(p1, p2.getInverseProperty());
			registerPropertyInclusion(p2, p1.getInverseProperty());
		}

		@Override
		public void visit(OWLSymmetricObjectPropertyAxiom arg0) {
			registerPropertyInclusion(arg0.getProperty(), arg0.getProperty().getInverseProperty());
		}

		@Override
		public void visit(OWLDataPropertyDomainAxiom arg0) {
			containsSomeFormOfNegation = classVisitor.containsSomeFormOfNegation(arg0.getDomain(), true);
		}

		@Override
		public void visit(OWLAsymmetricObjectPropertyAxiom arg0) {
			containsSomeFormOfNegation = true;
		}

		@Override
		public void visit(OWLDisjointClassesAxiom arg0) {
			containsSomeFormOfNegation = true;
		}

		@Override
		public void visit(OWLDifferentIndividualsAxiom arg0) {
			containsSomeFormOfNegation = true;
		}

		@Override
		public void visit(OWLDisjointDataPropertiesAxiom arg0) {
			containsSomeFormOfNegation = true;
		}

		@Override
		public void visit(OWLDisjointObjectPropertiesAxiom arg0) {
			containsSomeFormOfNegation = true;
		}

		@Override
		public void visit(OWLFunctionalObjectPropertyAxiom arg0) {
			containsSomeFormOfNegation = true;
		}

		@Override
		public void visit(OWLInverseFunctionalObjectPropertyAxiom arg0) {
			containsSomeFormOfNegation = true;
		}

		@Override
		public void visit(OWLDisjointUnionAxiom arg0) {
			containsSomeFormOfNegation = true;
		}

		@Override
		public void visit(OWLFunctionalDataPropertyAxiom arg0) {
			containsSomeFormOfNegation = true;
		}

		@Override
		public void visit(OWLIrreflexiveObjectPropertyAxiom arg0) {
			containsSomeFormOfNegation = true;
		}

		@Override
		public void visit(OWLEquivalentDataPropertiesAxiom arg0) {}

		@Override
		public void visit(OWLReflexiveObjectPropertyAxiom arg0) {
			generatingRoles.add(arg0.getProperty().getSimplified());
		}

		@Override
		public void visit(OWLDataPropertyRangeAxiom arg0) {}
		@Override
		public void visit(OWLTransitiveObjectPropertyAxiom arg0) {}
		@Override
		public void visit(OWLSubDataPropertyOfAxiom arg0) {}
		@Override
		public void visit(OWLSameIndividualAxiom arg0) {}
		@Override
		public void visit(OWLHasKeyAxiom arg0) {}
		@Override
		public void visit(OWLDatatypeDefinitionAxiom arg0) {}
		@Override
		public void visit(SWRLRule arg0) {}
		@Override
		public void visit(OWLDataPropertyAssertionAxiom arg0) {
			try{
				throw new IllegalAccessException("All assertions should have been previously filtered out " + arg0);
			}
			catch (Exception e){
				e.printStackTrace();
			}
		}

		@Override
		public void visit(OWLClassAssertionAxiom arg0) {
			try{
				throw new IllegalAccessException("All assertions should have been previously filtered out " + arg0);
			}
			catch (Exception e){
				e.printStackTrace();
			}
		}

		@Override
		public void visit(OWLObjectPropertyAssertionAxiom arg0) {
			try{
				throw new IllegalAccessException("All assertions should have been previously filtered out " + arg0);
			}
			catch (Exception e){
				e.printStackTrace();
			}
		}

		@Override
		public void visit(OWLNegativeDataPropertyAssertionAxiom arg0) {
			try{
				throw new IllegalAccessException("All assertions should have been previously filtered out " + arg0);
			}
			catch (Exception e){
				e.printStackTrace();
			}
		}

		@Override
		public void visit(OWLNegativeObjectPropertyAssertionAxiom arg0) {
			try{
				throw new IllegalAccessException("All assertions should have been previously filtered out " + arg0);
			}
			catch (Exception e){
				e.printStackTrace();
			}
		}
		@Override
		public void visit(OWLAnnotationAssertionAxiom arg0) {}
		@Override
		public void visit(OWLSubAnnotationPropertyOfAxiom arg0) {}
		@Override
		public void visit(OWLAnnotationPropertyDomainAxiom arg0) {}
		@Override
		public void visit(OWLAnnotationPropertyRangeAxiom arg0) {}
		@Override
		public void visit(OWLDeclarationAxiom arg0) {}


	}


	class ClassVisitor implements OWLClassExpressionVisitor{
		//for the equality predicate, we can consider as negation either = or !=
		//let us consider = as the one with the negative connotations

		protected boolean containsSomeFormOfNegation = false; 
		protected boolean signOfOccurrence = false;

		public boolean containsSomeFormOfNegation(OWLClassExpression c, boolean signOfOccurrence){
			this.signOfOccurrence = signOfOccurrence;
			c.accept(this);
			return containsSomeFormOfNegation;
		}

		@Override
		public void visit(OWLClass arg0) {
			containsSomeFormOfNegation = false;
		}

		@Override
		public void visit(OWLObjectIntersectionOf arg0) {
			boolean aux = false;
			boolean sign = signOfOccurrence;
			Iterator<OWLClassExpression> iter = arg0.getOperands().iterator();
			while (!aux && iter.hasNext()){
				aux = containsSomeFormOfNegation(iter.next(), sign);
			}
			containsSomeFormOfNegation = aux;
		}

		@Override
		public void visit(OWLObjectUnionOf arg0) {
			boolean aux = false;
			boolean sign = signOfOccurrence;
			Iterator<OWLClassExpression> iter = arg0.getOperands().iterator();
			while (!aux && iter.hasNext()){
				aux = containsSomeFormOfNegation(iter.next(), sign);
			}
			containsSomeFormOfNegation = aux;
		}

		@Override
		public void visit(OWLObjectComplementOf arg0) {
			containsSomeFormOfNegation = signOfOccurrence || containsSomeFormOfNegation(arg0.getComplementNNF(), true);
		}

		@Override
		public void visit(OWLObjectAllValuesFrom arg0) {
			if (signOfOccurrence){
				containsSomeFormOfNegation = containsSomeFormOfNegation(arg0.getFiller(), true);
				notForgettable.add(arg0.getProperty().getInverseProperty().getSimplified());
			}
			else{
				containsSomeFormOfNegation = containsSomeFormOfNegation(arg0.getFiller().getComplementNNF(), true);
				generatingRoles.add(arg0.getProperty().getSimplified());
			}
		}

		@Override
		public void visit(OWLObjectSomeValuesFrom arg0) {
			containsSomeFormOfNegation = containsSomeFormOfNegation(arg0.getFiller(), signOfOccurrence);
			if (!containsSomeFormOfNegation)
				if (signOfOccurrence)
					generatingRoles.add(arg0.getProperty().getSimplified());
				else
					notForgettable.add(arg0.getProperty().getSimplified());
				
		}

		@Override
		public void visit(OWLObjectHasValue arg0) {
			//this kind of occurrence of nominals by itself is ok, the problem comes in cases where a node
			//that wasn't originally an individual i becomes i by A->{i} and then inherits all concepts 
			//in the label of i
			//eg: A->{o}, B->some R.{o}, B->all R. C  implies A->C
			containsSomeFormOfNegation = false;
			if (signOfOccurrence)
				generatingRoles.add(arg0.getProperty().getSimplified());
			else
				notForgettable.add(arg0.getProperty().getSimplified());
		}

		@Override
		public void visit(OWLObjectMinCardinality arg0) {
			containsSomeFormOfNegation = containsSomeFormOfNegation(arg0.getFiller(), signOfOccurrence);
			if (!containsSomeFormOfNegation)
				if (signOfOccurrence)
					generatingRoles.add(arg0.getProperty().getSimplified());
				else
					notForgettable.add(arg0.getProperty().getSimplified());
		}

		@Override
		public void visit(OWLObjectExactCardinality arg0) {
			OWLClassExpression e = factory.getOWLObjectIntersectionOf(
					factory.getOWLObjectMinCardinality(arg0.getCardinality(), arg0.getProperty(), arg0.getFiller()),
					factory.getOWLObjectMaxCardinality(arg0.getCardinality(), arg0.getProperty(), arg0.getFiller()));
			containsSomeFormOfNegation(e, signOfOccurrence);
		}

		@Override
		public void visit(OWLObjectMaxCardinality arg0) {
			if (signOfOccurrence){
				containsSomeFormOfNegation = true;
			}
			else{
				if (!containsSomeFormOfNegation(arg0.getFiller(), true))
					generatingRoles.add(arg0.getProperty().getSimplified());
			}
		}

		@Override
		public void visit(OWLObjectHasSelf arg0) {
			containsSomeFormOfNegation = false;
			if (signOfOccurrence)
				generatingRoles.add(arg0.getProperty().getSimplified());
			else
				notForgettable.add(arg0.getProperty().getSimplified());
		}

		@Override
		public void visit(OWLObjectOneOf arg0) {
			containsSomeFormOfNegation = true;
		}

		@Override
		public void visit(OWLDataSomeValuesFrom arg0) {
			containsSomeFormOfNegation = false;
		}

		@Override
		public void visit(OWLDataAllValuesFrom arg0) {
			containsSomeFormOfNegation = false;
		}

		@Override
		public void visit(OWLDataHasValue arg0) {
			containsSomeFormOfNegation = false;
		}

		@Override
		public void visit(OWLDataMinCardinality arg0) {
			containsSomeFormOfNegation = false;
		}

		@Override
		public void visit(OWLDataExactCardinality arg0) {
			containsSomeFormOfNegation(factory.getOWLObjectIntersectionOf(
					factory.getOWLDataMinCardinality(arg0.getCardinality(), arg0.getProperty(), arg0.getFiller()),
					factory.getOWLDataMaxCardinality(arg0.getCardinality(), arg0.getProperty(), arg0.getFiller())), 
					signOfOccurrence);
		}

		@Override
		public void visit(OWLDataMaxCardinality arg0) {
			containsSomeFormOfNegation = signOfOccurrence;
		}
	}


	class AxiomRewriter implements OWLAxiomVisitor{
		
		Collection<OWLAxiom> axioms = new HashSet<OWLAxiom>();
		ClassRewriter classRewriter = new ClassRewriter(); 
		
		public Collection<OWLAxiom> getRewrittenAxiom(OWLAxiom ax){
			initAxioms(ax);
			ax.accept(this);
			return axioms;
		}

		protected void initAxioms(OWLAxiom ax){
			axioms.clear();
			axioms.add(ax);
		}
		
		@Override
		public void visit(OWLSubClassOfAxiom arg0) {
			axioms.clear();
			OWLClassExpression newSuperClass = classRewriter.getRewrittenClassExpression(arg0.getSuperClass(), true);
			if (!newSuperClass.isOWLThing()){
				OWLClassExpression newSubClass = classRewriter.getRewrittenClassExpression(arg0.getSubClass(), false);
				if (!newSubClass.isOWLNothing())
					axioms.add(factory.getOWLSubClassOfAxiom(newSubClass, newSuperClass));	
			}
		}

		@Override
		public void visit(OWLEquivalentClassesAxiom arg0) {
			if (arg0.getClassExpressions().size()>1) {
				Collection<OWLAxiom> aux = new HashSet<OWLAxiom>();
				Iterator<OWLClassExpression> iterator = arg0.getClassExpressions().iterator();
				OWLClassExpression first=iterator.next();
				OWLClassExpression last=first;
				while (iterator.hasNext()) {
					OWLClassExpression next=iterator.next();
					aux.addAll(getRewrittenAxiom(factory.getOWLSubClassOfAxiom(last, next)));
					last=next;
				}
				aux.addAll(getRewrittenAxiom(factory.getOWLSubClassOfAxiom(last, first)));
				
				axioms.clear();
				axioms = aux;
			}
			else
				return;
		}

		@Override
		public void visit(OWLObjectPropertyDomainAxiom arg0) {
			axioms.clear();
			OWLClassExpression newDomain = classRewriter.getRewrittenClassExpression(arg0.getDomain(), true);
			if (!newDomain.isOWLThing())
				axioms.add(factory.getOWLObjectPropertyDomainAxiom(arg0.getProperty(), newDomain));
		}

		@Override
		public void visit(OWLObjectPropertyRangeAxiom arg0) {
			axioms.clear();
			OWLObjectPropertyExpression p = arg0.getProperty().getSimplified();
			OWLObjectPropertyExpression pInv = p.getInverseProperty().getSimplified();
			if (rolesWithSomeNotForgettableSubproperty.contains(p) || generatingRoles.contains(pInv)){
				OWLClassExpression newRange = classRewriter.getRewrittenClassExpression(arg0.getRange(), true);
				if (!newRange.isOWLThing())
					axioms.add(factory.getOWLObjectPropertyRangeAxiom(arg0.getProperty(), newRange));
			}
		}
		
		@Override
		public void visit(OWLDataPropertyDomainAxiom arg0) {
			axioms.clear();
			OWLClassExpression newDomain = classRewriter.getRewrittenClassExpression(arg0.getDomain(), true);
			if (!newDomain.isOWLThing())
				axioms.add(factory.getOWLDataPropertyDomainAxiom(arg0.getProperty(), newDomain));
		}

		@Override
		public void visit(OWLEquivalentObjectPropertiesAxiom arg0) {
			Set<OWLObjectPropertyExpression> aux = new HashSet<OWLObjectPropertyExpression>();
			for (OWLObjectPropertyExpression p : arg0.getProperties()){
				aux.add(p.getSimplified());
				aux.add(p.getInverseProperty().getSimplified());
			}
			aux.retainAll(rolesWithSomeNotForgettableSubproperty);
			if (aux.isEmpty())
				axioms.clear();
		}
		@Override
		public void visit(OWLSubObjectPropertyOfAxiom arg0) {
			Set<OWLObjectPropertyExpression> aux = new HashSet<OWLObjectPropertyExpression>();
			OWLObjectPropertyExpression p = arg0.getSubProperty();
			aux.add(p.getSimplified());
			aux.add(p.getInverseProperty().getSimplified());
			aux.retainAll(rolesWithSomeNotForgettableSubproperty);
			if (aux.isEmpty())
				axioms.clear();
		}
		@Override
		public void visit(OWLSymmetricObjectPropertyAxiom arg0) {
			Set<OWLObjectPropertyExpression> aux = new HashSet<OWLObjectPropertyExpression>();
			OWLObjectPropertyExpression p = arg0.getProperty();
			aux.add(p.getSimplified());
			aux.add(p.getInverseProperty().getSimplified());
			aux.retainAll(rolesWithSomeNotForgettableSubproperty);
			if (aux.isEmpty())
				axioms.clear();
		}
		@Override
		public void visit(OWLInverseObjectPropertiesAxiom arg0) {
			Set<OWLObjectPropertyExpression> aux = new HashSet<OWLObjectPropertyExpression>();
			OWLObjectPropertyExpression p = arg0.getFirstProperty();
			aux.add(p.getSimplified());
			aux.add(p.getInverseProperty().getSimplified());
			p = arg0.getSecondProperty();
			aux.add(p.getSimplified());
			aux.add(p.getInverseProperty().getSimplified());
			aux.retainAll(rolesWithSomeNotForgettableSubproperty);
			if (aux.isEmpty())
				axioms.clear();
		}
		@Override
		public void visit(OWLSubPropertyChainOfAxiom arg0) {
			Set<OWLObjectPropertyExpression> aux = new HashSet<OWLObjectPropertyExpression>();
			OWLObjectPropertyExpression p = arg0.getSuperProperty();
			aux.add(p.getSimplified());
			aux.add(p.getInverseProperty().getSimplified());
			aux.retainAll(rolesWithSomeNotForgettableSubproperty);
			if (aux.isEmpty())
				axioms.clear();
		}
		@Override
		public void visit(OWLReflexiveObjectPropertyAxiom arg0) {
			axioms.clear();
			OWLObjectPropertyExpression p = arg0.getProperty().getSimplified();
			OWLClassExpression e = onlyNotForgettableBecauseOfDomain.get(p);
			if (e != null){
				axioms.add(factory.getOWLSubClassOfAxiom(factory.getOWLThing(), e));
				return;
			}
			if (notForgettable.contains(p))
				axioms.add(arg0);
			//o.w. it's a Forgettable role so we don't need the axiom	
		}
		@Override
		public void visit(OWLAnnotationAssertionAxiom arg0) {}
		@Override
		public void visit(OWLSubAnnotationPropertyOfAxiom arg0) {}
		@Override
		public void visit(OWLAnnotationPropertyDomainAxiom arg0) {}
		@Override
		public void visit(OWLAnnotationPropertyRangeAxiom arg0) {}
		@Override
		public void visit(OWLDeclarationAxiom arg0) {}
		@Override
		public void visit(OWLEquivalentDataPropertiesAxiom arg0) {}
		@Override
		public void visit(OWLDataPropertyRangeAxiom arg0) {}
		@Override
		public void visit(OWLTransitiveObjectPropertyAxiom arg0) {}
		@Override
		public void visit(OWLSubDataPropertyOfAxiom arg0) {}
		@Override
		public void visit(OWLSameIndividualAxiom arg0) {}
		@Override
		public void visit(OWLHasKeyAxiom arg0) {}
		@Override
		public void visit(OWLDatatypeDefinitionAxiom arg0) {}
		@Override
		public void visit(SWRLRule arg0) {}
		@Override
		public void visit(OWLAsymmetricObjectPropertyAxiom arg0) {
			try{
				throw new IllegalAccessException("If this axiom is in the ontology the rewriting technique should not be applied " + arg0.toString());
			}
			catch (Exception e){
				e.printStackTrace();
			}
		}
		@Override
		public void visit(OWLDisjointClassesAxiom arg0) {
			try{
				throw new IllegalAccessException("If this axiom is in the ontology the rewriting technique should not be applied " + arg0.toString());
			}
			catch (Exception e){
				e.printStackTrace();
			}
		}
		@Override
		public void visit(OWLDifferentIndividualsAxiom arg0) {
			try{
				throw new IllegalAccessException("If this axiom is in the ontology the rewriting technique should not be applied " + arg0.toString());
			}
			catch (Exception e){
				e.printStackTrace();
			}
		}
		@Override
		public void visit(OWLDisjointDataPropertiesAxiom arg0) {
			try{
				throw new IllegalAccessException("If this axiom is in the ontology the rewriting technique should not be applied " + arg0.toString());
			}
			catch (Exception e){
				e.printStackTrace();
			}
		}
		@Override
		public void visit(OWLDisjointObjectPropertiesAxiom arg0) {
			try{
				throw new IllegalAccessException("If this axiom is in the ontology the rewriting technique should not be applied " + arg0.toString());
			}
			catch (Exception e){
				e.printStackTrace();
			}
		}
		@Override
		public void visit(OWLFunctionalObjectPropertyAxiom arg0) {
			try{
				throw new IllegalAccessException("If this axiom is in the ontology the rewriting technique should not be applied " + arg0.toString());
			}
			catch (Exception e){
				e.printStackTrace();
			}
		}
		@Override
		public void visit(OWLInverseFunctionalObjectPropertyAxiom arg0) {
			try{
				throw new IllegalAccessException("If this axiom is in the ontology the rewriting technique should not be applied " + arg0.toString());
			}
			catch (Exception e){
				e.printStackTrace();
			}
		}
		@Override
		public void visit(OWLDisjointUnionAxiom arg0) {
			try{
				throw new IllegalAccessException("If this axiom is in the ontology the rewriting technique should not be applied " + arg0.toString());
			}
			catch (Exception e){
				e.printStackTrace();
			}
		}
		@Override
		public void visit(OWLFunctionalDataPropertyAxiom arg0) {
			try{
				throw new IllegalAccessException("If this axiom is in the ontology the rewriting technique should not be applied " + arg0.toString());
			}
			catch (Exception e){
				e.printStackTrace();
			}
		}
		@Override
		public void visit(OWLIrreflexiveObjectPropertyAxiom arg0) {
			try{
				throw new IllegalAccessException("If this axiom is in the ontology the rewriting technique should not be applied " + arg0.toString());
			}
			catch (Exception e){
				e.printStackTrace();
			}
		}
		@Override
		public void visit(OWLDataPropertyAssertionAxiom arg0) {
			try{
				throw new IllegalAccessException("All assertions should have been previously filtered out " + arg0);
			}
			catch (Exception e){
				e.printStackTrace();
			}
		}
		@Override
		public void visit(OWLClassAssertionAxiom arg0) {
			try{
				throw new IllegalAccessException("All assertions should have been previously filtered out " + arg0);
			}
			catch (Exception e){
				e.printStackTrace();
			}
		}
		@Override
		public void visit(OWLObjectPropertyAssertionAxiom arg0) {
			try{
				throw new IllegalAccessException("All assertions should have been previously filtered out " + arg0);
			}
			catch (Exception e){
				e.printStackTrace();
			}
		}
		@Override
		public void visit(OWLNegativeDataPropertyAssertionAxiom arg0) {
			try{
				throw new IllegalAccessException("All assertions should have been previously filtered out " + arg0);
			}
			catch (Exception e){
				e.printStackTrace();
			}
		}
		@Override
		public void visit(OWLNegativeObjectPropertyAssertionAxiom arg0) {
			try{
				throw new IllegalAccessException("All assertions should have been previously filtered out " + arg0);
			}
			catch (Exception e){
				e.printStackTrace();
			}
		}
	}
	
	
	class ClassRewriter implements OWLClassExpressionVisitor{
		
		OWLClassExpression rewrittenExpression;
		boolean signOfOccurrence = false;
		
		public OWLClassExpression getRewrittenClassExpression(OWLClassExpression e, boolean signOfOccurrence){
			this.signOfOccurrence = signOfOccurrence;
			rewrittenExpression = e;
			e.accept(this);
			return rewrittenExpression;
		}

		@Override
		public void visit(OWLClass arg0) {}

		@Override
		public void visit(OWLObjectIntersectionOf arg0) {
			Set<OWLClassExpression> newOperands = new HashSet<OWLClassExpression>();
			boolean sign = signOfOccurrence;
			for (OWLClassExpression e : arg0.getOperands()){
				OWLClassExpression newOperand = getRewrittenClassExpression(e, sign);
				if (newOperand.isOWLNothing()){//A & bot = bot
					rewrittenExpression = newOperand;
					return;
				}
				else if (!newOperand.isOWLThing()) //A & top = A
					newOperands.add(newOperand);
			}
			if (newOperands.size() > 1)
				rewrittenExpression = factory.getOWLObjectIntersectionOf(newOperands);
			else if (newOperands.size() == 1)
				rewrittenExpression = newOperands.iterator().next();
			else
				rewrittenExpression = factory.getOWLThing();
		}

		@Override
		public void visit(OWLObjectUnionOf arg0) {
			Set<OWLClassExpression> newOperands = new HashSet<OWLClassExpression>();
			boolean sign = signOfOccurrence;
			for (OWLClassExpression e : arg0.getOperands()){
				OWLClassExpression newOperand = getRewrittenClassExpression(e, sign);
				if (newOperand.isOWLThing()){	//A or top = top
					rewrittenExpression = newOperand;
					return;
				}
				else if (!newOperand.isOWLNothing()) //A or bot = A 
					newOperands.add(newOperand);
			}
			if (newOperands.size() > 1)
				rewrittenExpression = factory.getOWLObjectUnionOf(newOperands);
			else if (newOperands.size() == 1)
				rewrittenExpression = newOperands.iterator().next();
			else
				rewrittenExpression = factory.getOWLNothing();
		}

		@Override
		public void visit(OWLObjectComplementOf arg0) {
			rewrittenExpression = factory.getOWLObjectComplementOf(getRewrittenClassExpression(arg0.getOperand(), !signOfOccurrence));
		}

		@Override
		public void visit(OWLObjectSomeValuesFrom arg0) {
			if (signOfOccurrence){
				if (forgettableRoles.contains(arg0.getProperty())){
					rewrittenExpression = factory.getOWLThing();
					nExistentialRestrictionsRewrittenAway++;
					return;
				}
				OWLClassExpression domain = onlyNotForgettableBecauseOfDomain.get(arg0.getProperty().getSimplified());
				if (signOfOccurrence && domain != null){
					rewrittenExpression = domain;
					nExistentialRestrictionsRewrittenAway++;
					return;
				}
			}
			rewrittenExpression = factory.getOWLObjectSomeValuesFrom(arg0.getProperty(), getRewrittenClassExpression(arg0.getFiller(), signOfOccurrence));
		}

		@Override
		public void visit(OWLObjectAllValuesFrom arg0) {
			//we only need to keep positive occurrences of     all R. A		if R is not forgettable or inv(R) is generating
			OWLObjectPropertyExpression p = arg0.getProperty().getSimplified();
			if (signOfOccurrence){
				OWLObjectPropertyExpression pInv = p.getInverseProperty().getSimplified();
				if (!rolesWithSomeNotForgettableSubproperty.contains(p) && !generatingRoles.contains(pInv))
					rewrittenExpression = factory.getOWLThing();
				else 
					rewrittenExpression = factory.getOWLObjectAllValuesFrom(p, getRewrittenClassExpression(arg0.getFiller(), signOfOccurrence));
			}
			else{
				//a negative occurrence of      all R. A    is basically a positive occurrence of    some R. not A
				//if A didn't contain some implicit negation then we wouldn't be applying the rewriting, therefore it does
				//so if the role is forgettable, we can replace this expression by top
				if (forgettableRoles.contains(p))
					rewrittenExpression = factory.getOWLThing();
				else {
					OWLClassExpression domain = onlyNotForgettableBecauseOfDomain.get(p); 
					if (domain != null)
						//we replace all R. E by the NNF of the domain of R. NOT REALLY 100% sure about this... TODO check theoretically if this is even correct
						rewrittenExpression = domain.getComplementNNF();
					else
						rewrittenExpression = factory.getOWLObjectAllValuesFrom(p, getRewrittenClassExpression(arg0.getFiller(), signOfOccurrence));
				}
			}
		}

		@Override
		public void visit(OWLObjectHasValue arg0) {
			if (signOfOccurrence && forgettableRoles.contains(arg0.getProperty())){
				rewrittenExpression = factory.getOWLThing();
				nExistentialRestrictionsRewrittenAway++;
			}
		}

		@Override
		public void visit(OWLObjectMinCardinality arg0) {
			if (signOfOccurrence){
				if (forgettableRoles.contains(arg0.getProperty())){
					rewrittenExpression = factory.getOWLThing();
					nExistentialRestrictionsRewrittenAway++;
					return;
				}
				OWLClassExpression domain = onlyNotForgettableBecauseOfDomain.get(arg0.getProperty().getSimplified());
				if (signOfOccurrence && domain != null){
					rewrittenExpression = domain;
					nExistentialRestrictionsRewrittenAway++;
					return;
				}
			}
			rewrittenExpression = factory.getOWLObjectMinCardinality(arg0.getCardinality(), arg0.getProperty(), getRewrittenClassExpression(arg0.getFiller(), signOfOccurrence)); 
		}

		@Override
		public void visit(OWLObjectExactCardinality arg0) {
			if (signOfOccurrence )
				try{
					throw new IllegalAccessException("If there is a positive occurrence of this class expression the rewriting technique should not be applied " + arg0.toString());
				}
				catch (Exception e){
					e.printStackTrace();
				}
			else{//the role involved cannot be forgettable because this expression involves a lhs minCard
				OWLClassExpression fillerRewAsRhs = getRewrittenClassExpression(arg0.getFiller(), true);
				OWLClassExpression fillerRewAsLhs = getRewrittenClassExpression(arg0.getFiller(), false);
				if (fillerRewAsLhs.equals(fillerRewAsRhs))
					rewrittenExpression = factory.getOWLObjectExactCardinality(arg0.getCardinality(), arg0.getProperty(), fillerRewAsLhs);
				else
					rewrittenExpression = factory.getOWLObjectIntersectionOf(
							factory.getOWLObjectMinCardinality(arg0.getCardinality(), arg0.getProperty(), fillerRewAsLhs),
							factory.getOWLObjectMaxCardinality(arg0.getCardinality(), arg0.getProperty(), fillerRewAsRhs));
			}
		}

		@Override
		public void visit(OWLObjectMaxCardinality arg0) {
			if (signOfOccurrence){
				try{
					throw new IllegalAccessException("If there is a positive occurrence of this class expression the rewriting technique should not be applied " + arg0.toString());
				}
				catch (Exception e){
					e.printStackTrace();
				}
			}
			else{ 
				//atmost n R. A -> __   is the same as    top -> atleast n+1 R. A or __
				OWLObjectPropertyExpression p = arg0.getProperty().getSimplified();
				if (forgettableRoles.contains(p)){
					//if R is forgettable then we want   top -> top
					rewrittenExpression = factory.getOWLNothing();
					return;
				}
				OWLClassExpression domain = onlyNotForgettableBecauseOfDomain.get(p);
				if (domain != null){
					//then we want   top -> domain or __
					rewrittenExpression = factory.getOWLObjectComplementOf(domain);
					return;
				}
				rewrittenExpression = factory.getOWLObjectMaxCardinality(arg0.getCardinality(), arg0.getProperty(), getRewrittenClassExpression(arg0.getFiller(), true));
			}
		}

		@Override
		public void visit(OWLObjectHasSelf arg0) {
			if (signOfOccurrence && forgettableRoles.contains(arg0.getProperty())){
				rewrittenExpression = factory.getOWLThing();
				nExistentialRestrictionsRewrittenAway++;
			}
		}

		@Override
		public void visit(OWLObjectOneOf arg0) {
		}
		@Override
		public void visit(OWLDataSomeValuesFrom arg0) {}
		@Override
		public void visit(OWLDataAllValuesFrom arg0) {}
		@Override
		public void visit(OWLDataHasValue arg0) {}
		@Override
		public void visit(OWLDataMinCardinality arg0) {}
		@Override
		public void visit(OWLDataExactCardinality arg0) {}
		@Override
		public void visit(OWLDataMaxCardinality arg0) {}
		
	}
	
}
