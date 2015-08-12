package org.semanticweb.more.visitors;


import java.util.Iterator;
import java.util.Set;
import org.semanticweb.owlapi.model.*;


public class ELAxiomVisitor implements OWLFragmentVisitor {

	private boolean isEL;
	

	public boolean isEL() {
		return isEL;
	}
		
	public boolean isInFragment() {
		return isEL;
	}

	/*
	 * axioms in OWL 2 EL profile
	 */
	
	public void visit(OWLSubClassOfAxiom axiom){
		
		ELClassExpressionVisitor classExpVisitor = new ELClassExpressionVisitor();
		OWLClassExpression classExp = axiom.getSubClass();
		classExp.accept(classExpVisitor);
				
		//if the subclass in the axiom is not EL we do not need to check the superclass
		if (classExpVisitor.getIsEL()){ 
			classExp = axiom.getSuperClass();
			//classExpVisitor = new ELClassExpressionVisitor();
			classExp.accept(classExpVisitor);
		}
		
		isEL = classExpVisitor.getIsEL();
	}
	
	public void visit(OWLEquivalentClassesAxiom axiom){
		//We turn this OWLEquivalentClassesAxiom into a set of OWLSubClassOfAxiom and then use 
		//a new ELAxiomVisitor to visit them until we find one that is not EL
		Set<OWLSubClassOfAxiom> subClassOfAxioms = axiom.asOWLSubClassOfAxioms();		
		
		//We walk through the set of OWLSubClassOfAxiom with the help of in iterator
		Iterator<OWLSubClassOfAxiom> iterator = subClassOfAxioms.iterator();
		OWLSubClassOfAxiom oneSubClassOfAxiom = iterator.next();
		oneSubClassOfAxiom.accept(this);
		boolean isELSoFar = isEL;
		
		while(iterator.hasNext() && isELSoFar){
			oneSubClassOfAxiom = iterator.next();
			oneSubClassOfAxiom.accept(this);
			isELSoFar = isELSoFar && isEL;
		}
		isEL = isELSoFar;
	}
	
	public void visit(OWLDisjointClassesAxiom axiom) {
		Set<OWLClassExpression> exps = axiom.getClassExpressions();
		
		Iterator<OWLClassExpression> iterator = exps.iterator();
		
		boolean allEL = true;
		OWLClassExpression exp;
		ELClassExpressionVisitor classExpVisitor = new ELClassExpressionVisitor();
		
		while (allEL & iterator.hasNext()){
			exp = iterator.next();
			
			exp.accept(classExpVisitor);
			allEL = classExpVisitor.getIsEL();
		}
		
		isEL = allEL;
	}
	
	public void visit(OWLSubObjectPropertyOfAxiom axiom) {
		isEL = !(axiom.getSubProperty().isAnonymous()) && !(axiom.getSuperProperty().isAnonymous());//no inv(R) expressions allowed
	}
	
	public void visit(OWLSubPropertyChainOfAxiom axiom) {
		isEL = true;
		for (OWLObjectPropertyExpression prop : axiom.getPropertyChain()){
			isEL = isEL && !(prop.isAnonymous());
		}
		isEL = isEL && !(axiom.getSuperProperty().isAnonymous());
	}
	
	public void visit(OWLSubDataPropertyOfAxiom axiom) {
		isEL = !(axiom.getSubProperty().isAnonymous()) && !(axiom.getSuperProperty().isAnonymous());//no inv(R) expressions allowed
	}
	
	public void visit(OWLEquivalentObjectPropertiesAxiom axiom) {
		isEL = true;
		for (OWLObjectPropertyExpression prop : axiom.getProperties()){
			isEL = isEL && !(prop.isAnonymous());
		}
	}
	
	public void visit(OWLEquivalentDataPropertiesAxiom axiom) {
		isEL = true;
		for (OWLDataPropertyExpression prop : axiom.getProperties()){
			isEL = isEL && !(prop.isAnonymous());
		}
	}
	
	public void visit(OWLTransitiveObjectPropertyAxiom axiom) {
		isEL = !(axiom.getProperty().isAnonymous());
	}
	
	public void visit(OWLReflexiveObjectPropertyAxiom axiom) {
		isEL = !(axiom.getProperty().isAnonymous());
	}
		
	public void visit(OWLObjectPropertyDomainAxiom axiom) {
		isEL = !(axiom.getProperty().isAnonymous());
		if (isEL){
			ELClassExpressionVisitor classExpVisitor = new ELClassExpressionVisitor();
			axiom.getDomain().accept(classExpVisitor);
			isEL = classExpVisitor.getIsEL();              
		}
	}

	public void visit(OWLDataPropertyDomainAxiom axiom) {
		isEL = !(axiom.getProperty().isAnonymous());
		if (isEL){
			ELClassExpressionVisitor classExpVisitor = new ELClassExpressionVisitor();
			axiom.getDomain().accept(classExpVisitor);
			isEL = classExpVisitor.getIsEL();              
		}
	}
	
	public void visit(OWLObjectPropertyRangeAxiom axiom) {
		isEL = !(axiom.getProperty().isAnonymous());
		if (isEL){
			ELClassExpressionVisitor classExpVisitor = new ELClassExpressionVisitor();
			axiom.getRange().accept(classExpVisitor);
			isEL = classExpVisitor.getIsEL();              
		}
	}
	
	public void visit(OWLDataPropertyRangeAxiom axiom) {
		isEL = !(axiom.getProperty().isAnonymous());
	}
	
	public void visit(OWLFunctionalDataPropertyAxiom axiom) {
		isEL = !(axiom.getProperty().isAnonymous());
	}
	
	public void visit(OWLHasKeyAxiom axiom) {
		isEL = true;
		for (OWLPropertyExpression<?,?> prop : axiom.getPropertyExpressions()){
			isEL = isEL && !(prop.isAnonymous());
		}
		if (isEL){
			ELClassExpressionVisitor classExpVisitor = new ELClassExpressionVisitor();
			axiom.getClassExpression().accept(classExpVisitor);
			isEL = classExpVisitor.getIsEL();              
		}
	}
	
	public void visit(OWLDeclarationAxiom axiom) {
		isEL = true;
	}	
	/*
	 * END AXIOMS IN OWL 2 EL
	 */

	
	/*
	 * TERMINOLOGICAL AXIOMS NOT IN OWL 2 EL
	 */
	public void visit(OWLAsymmetricObjectPropertyAxiom axiom) {
		isEL = false;
	}

	public void visit(OWLDisjointDataPropertiesAxiom axiom) {
		isEL = false;
	}

	public void visit(OWLDisjointObjectPropertiesAxiom axiom) {
		isEL = false;
	}

	public void visit(OWLFunctionalObjectPropertyAxiom axiom) {
		isEL = false;
	}

	public void visit(OWLDisjointUnionAxiom axiom) {
		isEL = false;
	}

	public void visit(OWLSymmetricObjectPropertyAxiom axiom) {
		isEL = false;
	}
	
	public void visit(OWLIrreflexiveObjectPropertyAxiom axiom) {
		isEL = false;
	}

	public void visit(OWLInverseFunctionalObjectPropertyAxiom axiom) {
		isEL = false;
	}

	public void visit(OWLInverseObjectPropertiesAxiom axiom) {
		isEL = false;
	}
	
	public void visit(OWLDatatypeDefinitionAxiom axiom) {		
		isEL = false;
	}
	
	//should we ignore this??
	public void visit(SWRLRule axiom) {
		isEL = false;
	}
	
	/*
	 * END: TERMINOLOGICAL AXIOMS NOT IN OWL 2 EL
	 */	
	
	
	/*
	 * ASSERTION/ANNOTATION AXIOMS
	 */
	
	public void visit(OWLAnnotationAssertionAxiom axiom) {
		isEL = false;
	}

	public void visit(OWLSubAnnotationPropertyOfAxiom axiom) {
		isEL = false;
	}

	public void visit(OWLAnnotationPropertyDomainAxiom axiom) {
		isEL = false;
	}

	public void visit(OWLAnnotationPropertyRangeAxiom axiom) {
		isEL = false;
	}
	
	public void visit(OWLClassAssertionAxiom axiom) {
		isEL = false;
	}
	
	public void visit(OWLObjectPropertyAssertionAxiom axiom) {
		isEL = false;
	}

	public void visit(OWLDataPropertyAssertionAxiom axiom) {
		isEL = false;
	}
	
	public void visit(OWLNegativeObjectPropertyAssertionAxiom axiom) {
		isEL = false;
	}
	
	public void visit(OWLNegativeDataPropertyAssertionAxiom axiom) {
		isEL = false;
	}

	public void visit(OWLSameIndividualAxiom axiom) {
		isEL = false;
	}
	
	public void visit(OWLDifferentIndividualsAxiom axiom) {
		isEL = false;
	}
	
	/*
	 * END: ASSERTION/ANNOTATION AXIOMS
	 */
	
	
	protected class ELClassExpressionVisitor implements OWLClassExpressionVisitor {
		
		private boolean isEL;
		
		
		public boolean getIsEL(){
			return isEL;
		}

		public void visit(OWLClass exp){
			isEL = !exp.isOWLNothing();
		}
		
		public void visit(OWLObjectSomeValuesFrom exp){
			OWLObjectPropertyExpression propertyExp = exp.getProperty();
			OWLClassExpression classExp = exp.getFiller();
			classExp.accept(this);
			isEL = (!propertyExp.isAnonymous()) && this.getIsEL();
		}

		public void visit(OWLDataSomeValuesFrom exp) {
			isEL = !(exp.getProperty().isAnonymous());
		}
		
		public void visit(OWLDataHasValue exp) {
			isEL = !(exp.getProperty().isAnonymous());
		}
		
		public void visit(OWLObjectHasValue exp) {
			isEL = !(exp.getProperty().isAnonymous());
		}
		
		public void visit(OWLObjectHasSelf exp) {
			isEL = !(exp.getProperty().isAnonymous());
		}
		
		public void visit(OWLObjectOneOf exp) {
			isEL = (exp.getIndividuals().size() < 2);
		}
		
		public void visit(OWLDataOneOf exp) {
			isEL = (exp.getValues().size() < 2);
		}

		public  void visit(OWLObjectIntersectionOf exp){
			Set<OWLClassExpression> conjuncts = exp.asConjunctSet();
			Iterator<OWLClassExpression> iterator = conjuncts.iterator();
			OWLClassExpression classExp = iterator.next();
			
			classExp.accept(this);
			boolean allELSoFar = this.getIsEL();
			
			while (iterator.hasNext() && allELSoFar){
				classExp = iterator.next();
				classExp.accept(this);
				allELSoFar = allELSoFar && this.getIsEL();
			}
			isEL = allELSoFar;
		}
		
		
		public void visit(OWLDataIntersectionOf exp) {
			isEL = true;
		}

		
		
		/*
		 * not supported
		 */
		public void visit(OWLObjectUnionOf exp) {
			//System.out.println("Union");
			isEL = false;
		}

		public void visit(OWLObjectComplementOf exp) {
			//System.out.println("Complement");
			isEL = false;
		}
		
		public void visit(OWLObjectAllValuesFrom exp) {
			//System.out.println("All");
			isEL = false;
		}
		
		public void visit(OWLObjectMinCardinality exp) {
			//System.out.println("Card");
			isEL = false;
		}

		public void visit(OWLObjectExactCardinality exp) {
			//System.out.println("Card");
			isEL = false;
		}

		public void visit(OWLObjectMaxCardinality exp) {
			//System.out.println("Card");
			isEL = false;
		}

		public void visit(OWLDataAllValuesFrom exp) {
			//System.out.println("All");
			isEL = false;
		}

		public void visit(OWLDataMinCardinality exp) {
			//System.out.println("Card");
			isEL = false;
		}
		
		public void visit(OWLDataExactCardinality exp) {
			//System.out.println("Card");
			isEL = false;
		}

		public void visit(OWLDataMaxCardinality exp) {
			//System.out.println("Card");
			isEL = false;
		}

	}
	
}