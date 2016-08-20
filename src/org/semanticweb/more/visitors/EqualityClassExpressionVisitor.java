package org.semanticweb.more.visitors;

import java.util.Iterator;

import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLClassExpressionVisitor;
import org.semanticweb.owlapi.model.OWLDataAllValuesFrom;
import org.semanticweb.owlapi.model.OWLDataExactCardinality;
import org.semanticweb.owlapi.model.OWLDataHasValue;
import org.semanticweb.owlapi.model.OWLDataMaxCardinality;
import org.semanticweb.owlapi.model.OWLDataMinCardinality;
import org.semanticweb.owlapi.model.OWLDataSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectExactCardinality;
import org.semanticweb.owlapi.model.OWLObjectHasSelf;
import org.semanticweb.owlapi.model.OWLObjectHasValue;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectMaxCardinality;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectOneOf;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;

public class EqualityClassExpressionVisitor implements OWLClassExpressionVisitor{

	
	boolean containsEquality;
	
	public boolean containsEquality(OWLClassExpression ce){
		containsEquality = false;
		ce.accept(this);
		return containsEquality;
	}
	
	
	
	@Override
	public void visit(OWLObjectIntersectionOf arg0) {
		boolean ret = false;
		Iterator<OWLClassExpression> iter = arg0.getOperands().iterator();
		while (!ret && iter.hasNext())
			ret = containsEquality(iter.next());
	}

	@Override
	public void visit(OWLObjectUnionOf arg0) {
		boolean ret = false;
		Iterator<OWLClassExpression> iter = arg0.getOperands().iterator();
		while (!ret && iter.hasNext())
			ret = containsEquality(iter.next());
	}

	@Override
	public void visit(OWLObjectComplementOf arg0) {
		containsEquality(arg0.getOperand());
	}

	@Override
	public void visit(OWLObjectSomeValuesFrom arg0) {
		containsEquality(arg0.getFiller());
	}

	@Override
	public void visit(OWLObjectAllValuesFrom arg0) {
		containsEquality(arg0.getFiller());
	}

	@Override
	public void visit(OWLClass arg0) {
		containsEquality = false;
	}

	@Override
	public void visit(OWLObjectHasValue arg0) {
		containsEquality = false;
	}

	@Override
	public void visit(OWLObjectHasSelf arg0) {
		containsEquality = false;
	}

	@Override
	public void visit(OWLDataSomeValuesFrom arg0) {
		containsEquality = false;
	}

	@Override
	public void visit(OWLDataAllValuesFrom arg0) {
		containsEquality = false;
	}

	@Override
	public void visit(OWLDataHasValue arg0) {
		containsEquality = false;
	}

	@Override
	public void visit(OWLObjectMinCardinality arg0) {
		containsEquality = true;
	}

	@Override
	public void visit(OWLObjectExactCardinality arg0) {
		containsEquality = true;
	}

	@Override
	public void visit(OWLObjectMaxCardinality arg0) {
		containsEquality = true;
	}
	
	@Override
	public void visit(OWLObjectOneOf arg0) {
		containsEquality = true;
	}

	@Override
	public void visit(OWLDataMinCardinality arg0) {
		containsEquality = true;
	}

	@Override
	public void visit(OWLDataExactCardinality arg0) {
		containsEquality = true;
	}

	@Override
	public void visit(OWLDataMaxCardinality arg0) {
		containsEquality = true;
	}

}
