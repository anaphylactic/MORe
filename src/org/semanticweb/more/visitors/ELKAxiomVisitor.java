package org.semanticweb.more.visitors;

import java.util.Iterator;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLAnnotationAssertionAxiom;
import org.semanticweb.owlapi.model.OWLAnnotationPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLAnnotationPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLAsymmetricObjectPropertyAxiom;

import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLClassExpressionVisitor;
import org.semanticweb.owlapi.model.OWLDataAllValuesFrom;
import org.semanticweb.owlapi.model.OWLDataExactCardinality;
import org.semanticweb.owlapi.model.OWLDataHasValue;
import org.semanticweb.owlapi.model.OWLDataIntersectionOf;
import org.semanticweb.owlapi.model.OWLDataMaxCardinality;
import org.semanticweb.owlapi.model.OWLDataMinCardinality;
import org.semanticweb.owlapi.model.OWLDataOneOf;
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
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
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


public class ELKAxiomVisitor implements OWLFragmentVisitor {
	//this class checks whether an axiom is or not supported by the reasoner ELK
	
	private boolean isSupportedByELK;
	

	public boolean isInFragment() {
		return isSupportedByELK;
	}
		
	/*
	 * axioms supported by ELK
	 */
	
	public void visit(OWLSubClassOfAxiom axiom){
		ELKClassExpressionVisitor classExpVisitor = new ELKClassExpressionVisitor();
		isSupportedByELK = classExpVisitor.isSupportedByELK(axiom.getSubClass(),ELKClassExpressionVisitor.sub) &&
				classExpVisitor.isSupportedByELK(axiom.getSuperClass(),ELKClassExpressionVisitor.sup);
	}
	
	public void visit(OWLEquivalentClassesAxiom axiom){
		//We turn this OWLEquivalentClassesAxiom into a set of OWLSubClassOfAxiom and then use 
		//a new ELAxiomVisitor to visit them until we find one that is not EL
		Set<OWLSubClassOfAxiom> subClassOfAxioms = axiom.asOWLSubClassOfAxioms();		
		
		//We walk through the set of OWLSubClassOfAxiom with the help of an iterator
		Iterator<OWLSubClassOfAxiom> iterator = subClassOfAxioms.iterator();
		OWLSubClassOfAxiom oneSubClassOfAxiom = iterator.next();
		oneSubClassOfAxiom.accept(this);
		boolean isSupportedByELKSoFar = isSupportedByELK;
		
		while(iterator.hasNext() && isSupportedByELKSoFar){
			oneSubClassOfAxiom = iterator.next();
			oneSubClassOfAxiom.accept(this);
			isSupportedByELKSoFar = isSupportedByELKSoFar && isSupportedByELK;
		}
		isSupportedByELK = isSupportedByELKSoFar;
	}
	
	public void visit(OWLDisjointClassesAxiom axiom) {
		Set<OWLClassExpression> exps = axiom.getClassExpressions();
		Iterator<OWLClassExpression> iterator = exps.iterator();
		isSupportedByELK = true;
		ELKClassExpressionVisitor classExpVisitor = new ELKClassExpressionVisitor();
		
		while (isSupportedByELK & iterator.hasNext())
			isSupportedByELK = classExpVisitor.isSupportedByELK(iterator.next(), ELKClassExpressionVisitor.none);
	}
	
	public void visit(OWLSubObjectPropertyOfAxiom axiom) {
		isSupportedByELK = !(axiom.getSubProperty().isAnonymous()) && !(axiom.getSuperProperty().isAnonymous());//no inv(R) expressions allowed
	}
	
	public void visit(OWLSubPropertyChainOfAxiom axiom) {
		isSupportedByELK = true;
		for (OWLObjectPropertyExpression prop : axiom.getPropertyChain()){
			isSupportedByELK = isSupportedByELK && !(prop.isAnonymous());
		}
		isSupportedByELK = isSupportedByELK && !(axiom.getSuperProperty().isAnonymous());
	}
	
	public void visit(OWLSubDataPropertyOfAxiom axiom) {
		isSupportedByELK = false; //not yet supported by ELK
	}
	
	public void visit(OWLEquivalentObjectPropertiesAxiom axiom) {
		isSupportedByELK = true;
		for (OWLObjectPropertyExpression prop : axiom.getProperties()){
			isSupportedByELK = isSupportedByELK && !(prop.isAnonymous());
		}
	}
	
	public void visit(OWLEquivalentDataPropertiesAxiom axiom) {
		isSupportedByELK = false;//not yet supported by ELK
	}
	
	public void visit(OWLTransitiveObjectPropertyAxiom axiom) {
		isSupportedByELK = !(axiom.getProperty().isAnonymous());
	}
	
	public void visit(OWLReflexiveObjectPropertyAxiom axiom) {
		isSupportedByELK = !(axiom.getProperty().isAnonymous());
	}
		
	public void visit(OWLObjectPropertyDomainAxiom axiom) {
		isSupportedByELK = !(axiom.getProperty().isAnonymous());
		if (isSupportedByELK){
			ELKClassExpressionVisitor classExpVisitor = new ELKClassExpressionVisitor();
			isSupportedByELK = classExpVisitor.isSupportedByELK(axiom.getDomain(), ELKClassExpressionVisitor.none);              
		}
	}
	
	public void visit(OWLDeclarationAxiom axiom) {
		isSupportedByELK = true;
	}	
	/*
	 * END AXIOMS SUPPORTED BY ELK REASONER
	 */



	public void visit(OWLDataPropertyDomainAxiom axiom) {
		isSupportedByELK = false;//not yet supported by ELK
	}
	
	public void visit(OWLObjectPropertyRangeAxiom axiom) {
		isSupportedByELK = false;//not yet supported by ELK
	}
	
	public void visit(OWLDataPropertyRangeAxiom axiom) {
		isSupportedByELK = false;//not yet supported by ELK
	}
	
	public void visit(OWLFunctionalDataPropertyAxiom axiom) {
		isSupportedByELK = false;//not yet supported by ELK
	}
	
	public void visit(OWLHasKeyAxiom axiom) {
		isSupportedByELK = false;//not yet supported by ELK
	}
	
	/*
	 * TERMINOLOGICAL AXIOMS NOT SUPPORTED BY ELK REASONER
	 */
	public void visit(OWLAsymmetricObjectPropertyAxiom axiom) {
		isSupportedByELK = false;
	}

	public void visit(OWLDisjointDataPropertiesAxiom axiom) {
		isSupportedByELK = false;
	}

	public void visit(OWLDisjointObjectPropertiesAxiom axiom) {
		isSupportedByELK = false;
	}

	public void visit(OWLFunctionalObjectPropertyAxiom axiom) {
		isSupportedByELK = false;
	}

	public void visit(OWLDisjointUnionAxiom axiom) {
		isSupportedByELK = false;
	}

	public void visit(OWLSymmetricObjectPropertyAxiom axiom) {
		isSupportedByELK = false;
	}
	
	public void visit(OWLIrreflexiveObjectPropertyAxiom axiom) {
		isSupportedByELK = false;
	}

	public void visit(OWLInverseFunctionalObjectPropertyAxiom axiom) {
		isSupportedByELK = false;
	}

	public void visit(OWLInverseObjectPropertiesAxiom axiom) {
		isSupportedByELK = false;
	}
	
	public void visit(OWLDatatypeDefinitionAxiom axiom) {		
		isSupportedByELK = false;
	}
	
	//should we ignore this??
	public void visit(SWRLRule axiom) {
		isSupportedByELK = false;
	}
	
	/*
	 * END: TERMINOLOGICAL AXIOMS NOT SUPPORTED BY ELK REASONER
	 */	
	
	
	/*
	 * ASSERTION/ANNOTATION AXIOMS (IGNORED AXIOMS)
	 */
	
	public void visit(OWLAnnotationAssertionAxiom axiom) {
		isSupportedByELK = false;
	}

	public void visit(OWLSubAnnotationPropertyOfAxiom axiom) {
		isSupportedByELK = false;
	}

	public void visit(OWLAnnotationPropertyDomainAxiom axiom) {
		isSupportedByELK = false;
	}

	public void visit(OWLAnnotationPropertyRangeAxiom axiom) {
		isSupportedByELK = false;
	}
	
	public void visit(OWLClassAssertionAxiom axiom) {
		isSupportedByELK = false;
	}
	
	public void visit(OWLObjectPropertyAssertionAxiom axiom) {
		isSupportedByELK = false;
	}

	public void visit(OWLDataPropertyAssertionAxiom axiom) {
		isSupportedByELK = false;
	}
	
	public void visit(OWLNegativeObjectPropertyAssertionAxiom axiom) {
		isSupportedByELK = false;
	}
	
	public void visit(OWLNegativeDataPropertyAssertionAxiom axiom) {
		isSupportedByELK = false;
	}

	public void visit(OWLSameIndividualAxiom axiom) {
		isSupportedByELK = false;
	}
	
	public void visit(OWLDifferentIndividualsAxiom axiom) {
		isSupportedByELK = false;
	}
	
	/*
	 * END: ASSERTION/ANNOTATION AXIOMS (IGNORED AXIOMS)
	 */
	
	
	protected class ELKClassExpressionVisitor implements OWLClassExpressionVisitor {
		
		private boolean isSupportedByELK;
		private int subOrSuperClass;
		final static int none = 0;
		final static int sub = 1;
		final static int sup = 2;
		//0 neither, 1 subclass, 2 superclass
		
		
		public boolean isSupportedByELK(OWLClassExpression e, int isSubOrSuperClass){
			subOrSuperClass = isSubOrSuperClass;
			e.accept(this);
			return isSupportedByELK;
		}

		public void visit(OWLClass exp){
			isSupportedByELK = true;
		}
		
		public void visit(OWLObjectSomeValuesFrom exp){
			OWLObjectPropertyExpression propertyExp = exp.getProperty();
			OWLClassExpression filler = exp.getFiller();
			isSupportedByELK = (!propertyExp.isAnonymous()) && isSupportedByELK(filler, none);
		}

		public void visit(OWLDataSomeValuesFrom exp) {
			isSupportedByELK = false;//not yet supported by ELK
		}
		
		public void visit(OWLDataHasValue exp) {
			isSupportedByELK = !(exp.getProperty().isAnonymous());
		}
		
		public void visit(OWLObjectHasValue exp) {
			isSupportedByELK = !(exp.getProperty().isAnonymous());
		}
		
		public void visit(OWLObjectHasSelf exp) {
			isSupportedByELK = false;//not yet supported by ELK
		}
		
		public void visit(OWLObjectOneOf exp) {
			isSupportedByELK = false;//not yet supported by ELK
		}
		
		public void visit(OWLDataOneOf exp) {
			isSupportedByELK = false;//not yet supported by ELK
		}

		public  void visit(OWLObjectIntersectionOf exp){
			Set<OWLClassExpression> conjuncts = exp.asConjunctSet();
			Iterator<OWLClassExpression> iterator = conjuncts.iterator();
			OWLClassExpression classExp = iterator.next();
			boolean allELSoFar = this.isSupportedByELK(classExp, none);
			while (iterator.hasNext() && allELSoFar){
				classExp = iterator.next();
				allELSoFar = allELSoFar && this.isSupportedByELK(classExp, none);
			}
			isSupportedByELK = allELSoFar;
		}
		
		
		public void visit(OWLDataIntersectionOf exp) {
			isSupportedByELK = false;//not yet supported by ELK
		}

		
		
		public void visit(OWLObjectUnionOf exp) {
			//System.out.println("Union");
			isSupportedByELK = (subOrSuperClass == sub);
			if (isSupportedByELK){
				Set<OWLClassExpression> disjuncts = exp.asDisjunctSet();
				Iterator<OWLClassExpression> iterator = disjuncts.iterator();
				OWLClassExpression classExp = iterator.next();
				boolean allELSoFar = this.isSupportedByELK(classExp, none);
				
				while (iterator.hasNext() && allELSoFar){
					classExp = iterator.next();
					allELSoFar = allELSoFar && this.isSupportedByELK(classExp, none);
				}
				isSupportedByELK = allELSoFar;				
			}
		}

		public void visit(OWLObjectComplementOf exp) {
			//System.out.println("Complement");
			isSupportedByELK = (subOrSuperClass == sup);
			if (isSupportedByELK){
				isSupportedByELK = this.isSupportedByELK(exp.getOperand(), none);				
			}
		}
		
		
		/*
		 * not supported
		 */
		public void visit(OWLObjectAllValuesFrom exp) {
			//System.out.println("All");
			isSupportedByELK = false;
		}
		
		public void visit(OWLObjectMinCardinality exp) {
			//System.out.println("Card");
			isSupportedByELK = false;
		}

		public void visit(OWLObjectExactCardinality exp) {
			//System.out.println("Card");
			isSupportedByELK = false;
		}

		public void visit(OWLObjectMaxCardinality exp) {
			//System.out.println("Card");
			isSupportedByELK = false;
		}

		public void visit(OWLDataAllValuesFrom exp) {
			//System.out.println("All");
			isSupportedByELK = false;
		}

		public void visit(OWLDataMinCardinality exp) {
			//System.out.println("Card");
			isSupportedByELK = false;
		}
		
		public void visit(OWLDataExactCardinality exp) {
			//System.out.println("Card");
			isSupportedByELK = false;
		}

		public void visit(OWLDataMaxCardinality exp) {
			//System.out.println("Card");
			isSupportedByELK = false;
		}

	}
}