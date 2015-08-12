package org.semanticweb.more.visitors;

import java.util.Iterator;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLClassExpressionVisitor;
import org.semanticweb.owlapi.model.OWLDataAllValuesFrom;
import org.semanticweb.owlapi.model.OWLDataExactCardinality;
import org.semanticweb.owlapi.model.OWLDataHasValue;
import org.semanticweb.owlapi.model.OWLDataIntersectionOf;
import org.semanticweb.owlapi.model.OWLDataMaxCardinality;
import org.semanticweb.owlapi.model.OWLDataMinCardinality;
import org.semanticweb.owlapi.model.OWLDataOneOf;
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

public class SHIFClassExpressionVisitor implements OWLClassExpressionVisitor {
	
	private boolean isSHIF;
	
	
	public boolean isSHIF(OWLClassExpression exp){
		exp.accept(this);
		return isSHIF;
	}

	@Override
	public void visit(OWLClass exp){
		isSHIF = true;
	}
	
	@Override
	public void visit(OWLObjectSomeValuesFrom exp){
		isSHIF = isSHIF(exp.getFiller());
	}

	@Override
	public void visit(OWLDataSomeValuesFrom exp) {
		isSHIF = true;//????????
	}
	
	@Override
	public void visit(OWLDataHasValue exp) {
		isSHIF = false;//???
	}
	
	@Override
	public void visit(OWLObjectHasValue exp) {
		isSHIF = false;//????
	}
	
	@Override
	public void visit(OWLObjectHasSelf exp) {
		isSHIF = false;//?????	
	}
	
	@Override
	public void visit(OWLObjectOneOf exp) {
		isSHIF = false;
	}
	
	public void visit(OWLDataOneOf exp) {
		isSHIF = false;
	}

	@Override
	public  void visit(OWLObjectIntersectionOf exp){
		isSHIF = true;
		Set<OWLClassExpression> conjuncts = exp.asConjunctSet();
		Iterator<OWLClassExpression> iterator = conjuncts.iterator();
		while (iterator.hasNext() && isSHIF)
			isSHIF = isSHIF(iterator.next());
	}

	public void visit(OWLDataIntersectionOf exp) {
		isSHIF = true;//?????
	}

	
	/*
	 * not supported
	 */
	@Override
	public void visit(OWLObjectUnionOf exp) {
		isSHIF = true;
		Set<OWLClassExpression> exps = exp.getOperands();
		Iterator<OWLClassExpression> iterator = exps.iterator();
		while (isSHIF && iterator.hasNext())
			isSHIF = isSHIF(iterator.next());
	}

	@Override
	public void visit(OWLObjectComplementOf exp) {
		isSHIF = isSHIF(exp.getOperand());
	}
	
	@Override
	public void visit(OWLObjectAllValuesFrom exp) {
		isSHIF = isSHIF(exp.getFiller());
	}
	
	@Override
	public void visit(OWLObjectMinCardinality exp) {
		isSHIF = exp.getCardinality() == 1;
	}

	@Override
	public void visit(OWLObjectExactCardinality exp) {
		isSHIF = false;
	}

	@Override
	public void visit(OWLObjectMaxCardinality exp) {
		isSHIF = false;//could accept this as a negation, but then id have to take it into account when deciding if sth contains negations
	}

	@Override
	public void visit(OWLDataAllValuesFrom exp) {
		isSHIF = true;//????
	}

	@Override
	public void visit(OWLDataMinCardinality exp) {
		isSHIF = exp.getCardinality() == 1;//???
	}
	
	@Override
	public void visit(OWLDataExactCardinality exp) {
		isSHIF = false;
	}

	@Override
	public void visit(OWLDataMaxCardinality exp) {
		isSHIF = false;///idem as for Object
	}

}