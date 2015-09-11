package org.semanticweb.more.structural.inverseRewriting;

import java.util.Set;

import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLClassExpressionVisitor;
import org.semanticweb.owlapi.model.OWLDataAllValuesFrom;
import org.semanticweb.owlapi.model.OWLDataExactCardinality;
import org.semanticweb.owlapi.model.OWLDataFactory;
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
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;

public class RoleRewriter implements OWLClassExpressionVisitor {
    protected final OWLDataFactory m_factory=new OWLDataFactoryImpl();
    protected Set<OWLObjectPropertyExpression> nonRW;
    protected OWLClassExpression newClass;
    protected RoleOperations roleOps;
    
    public RoleRewriter(Set<OWLObjectPropertyExpression> nonRW, RoleOperations roleOps){
    	this.nonRW=nonRW; 	
    	this.roleOps = roleOps;
    }
	
    public void visit(OWLClass c){
		newClass=c;
	}
	
    public void visit(OWLObjectSomeValuesFrom object){
		OWLObjectPropertyExpression role=object.getProperty();
		OWLClassExpression filler=object.getFiller();
		newClass=m_factory.getOWLObjectSomeValuesFrom(roleOps.getNewRoleName(role, nonRW), filler);
	}
	
	
    public void visit(OWLObjectAllValuesFrom object){
		OWLObjectPropertyExpression role=object.getProperty();
		OWLClassExpression filler=object.getFiller();
		newClass=m_factory.getOWLObjectAllValuesFrom(roleOps.getNewRoleName(role, nonRW), filler);
		//System.out.println(newClass);
	}
	
    public void visit(OWLObjectMinCardinality object){
		OWLObjectPropertyExpression role=object.getProperty();
		OWLClassExpression filler=object.getFiller();
		int c=object.getCardinality();
		newClass=m_factory.getOWLObjectMinCardinality(c, roleOps.getNewRoleName(role, nonRW), filler);
	}
    
   	public void visit(OWLObjectMaxCardinality object) {
   		OWLObjectPropertyExpression role=object.getProperty();
		OWLClassExpression filler=object.getFiller();
		int c=object.getCardinality();
		newClass=m_factory.getOWLObjectMaxCardinality(c, roleOps.getNewRoleName(role, nonRW), filler);
	}


	@Override
	public void visit(OWLObjectIntersectionOf arg0) {
		newClass=arg0;
		
	}

	@Override
	public void visit(OWLObjectUnionOf arg0) {
		newClass=arg0;
		
	}

	@Override
	public void visit(OWLObjectComplementOf arg0) {
		newClass=arg0;
		
	}

	

	@Override
	public void visit(OWLObjectHasValue arg0) {
		newClass=arg0;
		
	}

	

	@Override
	public void visit(OWLObjectExactCardinality arg0) {
		newClass=arg0;
		
	}

	

	@Override
	public void visit(OWLObjectHasSelf arg0) {
		newClass=arg0;
		
	}

	@Override
	public void visit(OWLObjectOneOf arg0) {
		newClass=arg0;
		
	}

	@Override
	public void visit(OWLDataSomeValuesFrom arg0) {
		newClass=arg0;
		
	}

	@Override
	public void visit(OWLDataAllValuesFrom arg0) {
		newClass=arg0;
		
	}

	@Override
	public void visit(OWLDataHasValue arg0) {
		newClass=arg0;
		
	}

	@Override
	public void visit(OWLDataMinCardinality arg0) {
		newClass=arg0;
		
	}

	@Override
	public void visit(OWLDataExactCardinality arg0) {
		newClass=arg0;
		
	}

	@Override
	public void visit(OWLDataMaxCardinality arg0) {
		newClass=arg0;
		
	}

}
