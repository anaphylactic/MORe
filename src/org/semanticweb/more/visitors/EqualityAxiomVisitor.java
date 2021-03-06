package org.semanticweb.more.visitors;

import org.semanticweb.owlapi.model.OWLAnnotationAssertionAxiom;
import org.semanticweb.owlapi.model.OWLAnnotationPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLAnnotationPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLAsymmetricObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLAxiomVisitor;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyRangeAxiom;
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
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom;
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

public class EqualityAxiomVisitor implements OWLAxiomVisitor{

	
	boolean containsEquality;
	EqualityClassExpressionVisitor classExpVisitor = new EqualityClassExpressionVisitor();
	
	public boolean containsEquality(OWLAxiom ax){
		containsEquality = false;
		ax.accept(this);
		return containsEquality;
	}
	
	
	@Override
	public void visit(OWLDeclarationAxiom arg0) {}
	@Override
	public void visit(OWLSubClassOfAxiom arg0) {
		containsEquality = classExpVisitor.containsEquality(arg0.getSubClass()) ||
				classExpVisitor.containsEquality(arg0.getSuperClass());
	}

	
	@Override
	public void visit(OWLDisjointClassesAxiom arg0) {
		for (OWLClassExpression ce : arg0.getClassExpressions())
			if (containsEquality = classExpVisitor.containsEquality(ce))
				return;
	}

	@Override
	public void visit(OWLDataPropertyDomainAxiom arg0) {
		containsEquality = classExpVisitor.containsEquality(arg0.getDomain());
	}

	@Override
	public void visit(OWLObjectPropertyDomainAxiom arg0) {
		containsEquality = classExpVisitor.containsEquality(arg0.getDomain());
	}

	@Override
	public void visit(OWLObjectPropertyRangeAxiom arg0) {
		containsEquality = classExpVisitor.containsEquality(arg0.getRange());
	}

	@Override
	public void visit(OWLDisjointUnionAxiom arg0) {
		for (OWLClassExpression ce : arg0.getClassExpressions())
			if (containsEquality = classExpVisitor.containsEquality(ce))
				return;
	}

	@Override
	public void visit(OWLEquivalentClassesAxiom arg0) {
		for (OWLClassExpression ce : arg0.getClassExpressions())
			if (containsEquality = classExpVisitor.containsEquality(ce))
				return;
	}

	@Override
	public void visit(OWLAnnotationAssertionAxiom arg0) {
		containsEquality = true;
	}
	@Override
	public void visit(OWLSubAnnotationPropertyOfAxiom arg0) {
		containsEquality = true;
	}
	@Override
	public void visit(OWLAnnotationPropertyDomainAxiom arg0) {
		containsEquality = true;
	}
	@Override
	public void visit(OWLAnnotationPropertyRangeAxiom arg0) {
		containsEquality = true;
	}
	@Override
	public void visit(OWLNegativeObjectPropertyAssertionAxiom arg0) {
		containsEquality = true;
	}
	@Override
	public void visit(OWLNegativeDataPropertyAssertionAxiom arg0) {
		containsEquality = true;
	}
	@Override
	public void visit(OWLDifferentIndividualsAxiom arg0) {
		containsEquality = true;
	}
	@Override
	public void visit(OWLFunctionalObjectPropertyAxiom arg0) {
		containsEquality = true;
	}
	@Override
	public void visit(OWLFunctionalDataPropertyAxiom arg0) {
		containsEquality = true;
	}
	@Override
	public void visit(OWLClassAssertionAxiom arg0) {
		containsEquality = true;
	}
	@Override
	public void visit(OWLDataPropertyAssertionAxiom arg0) {
		containsEquality = true;
	}
	@Override
	public void visit(OWLInverseFunctionalObjectPropertyAxiom arg0) {
		containsEquality = true;
	}
	@Override
	public void visit(OWLSameIndividualAxiom arg0) {
		containsEquality = true;
	}

	
	@Override
	public void visit(OWLAsymmetricObjectPropertyAxiom arg0) {
		containsEquality = false;
	}
	@Override
	public void visit(OWLReflexiveObjectPropertyAxiom arg0) {
		containsEquality = false;
	}
	@Override
	public void visit(OWLEquivalentObjectPropertiesAxiom arg0) {
		containsEquality = false;
	}
	@Override
	public void visit(OWLDisjointDataPropertiesAxiom arg0) {
		containsEquality = false;
	}
	@Override
	public void visit(OWLDisjointObjectPropertiesAxiom arg0) {
		containsEquality = false;
	}
	@Override
	public void visit(OWLSubObjectPropertyOfAxiom arg0) {
		containsEquality = false;
	}
	@Override
	public void visit(OWLObjectPropertyAssertionAxiom arg0) {
		containsEquality = false;
	}
	@Override
	public void visit(OWLSymmetricObjectPropertyAxiom arg0) {
		containsEquality = false;
	}
	@Override
	public void visit(OWLDataPropertyRangeAxiom arg0) {
		containsEquality = false;
	}
	@Override
	public void visit(OWLEquivalentDataPropertiesAxiom arg0) {
		containsEquality = false;
	}
	@Override
	public void visit(OWLTransitiveObjectPropertyAxiom arg0) {
		containsEquality = false;		
	}
	@Override
	public void visit(OWLIrreflexiveObjectPropertyAxiom arg0) {
		containsEquality = false;
	}
	@Override
	public void visit(OWLSubDataPropertyOfAxiom arg0) {
		containsEquality = false;
	}
	@Override
	public void visit(OWLSubPropertyChainOfAxiom arg0) {
		containsEquality = false;
	}
	@Override
	public void visit(OWLInverseObjectPropertiesAxiom arg0) {
		containsEquality = false;
	}
	@Override
	public void visit(OWLHasKeyAxiom arg0) {
		containsEquality = false;
	}
	@Override
	public void visit(OWLDatatypeDefinitionAxiom arg0) {
		containsEquality = false;
	}
	@Override
	public void visit(SWRLRule arg0) {
		containsEquality = false;
	}

}
