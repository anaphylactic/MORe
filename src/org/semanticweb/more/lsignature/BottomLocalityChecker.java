package org.semanticweb.more.lsignature;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.semanticweb.more.reasoner.ListProcessor;
import org.semanticweb.more.reasoner.LocalityInfo;
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
import org.semanticweb.owlapi.model.OWLDataOneOf;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLDataPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyExpression;
import org.semanticweb.owlapi.model.OWLDataPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLDataSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLDatatypeDefinitionAxiom;
import org.semanticweb.owlapi.model.OWLDeclarationAxiom;
import org.semanticweb.owlapi.model.OWLDifferentIndividualsAxiom;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointDataPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointUnionAxiom;
import org.semanticweb.owlapi.model.OWLEntity;
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

public class BottomLocalityChecker implements OWLAxiomVisitor{
	
	private boolean isLocal;  
	private boolean canMakeLocal;
	private List<Set<OWLEntity>> solutions;
	
	protected Set<OWLEntity> externalSignature; 
	protected Set<OWLEntity> globalEntities;// we don't count any solutions containing global entities (don't really need to make any changes to the ListProcessor)
	
	private BottomChecker negativeVisitor;
	private TopChecker positiveVisitor;
	
	
	public BottomLocalityChecker(){
		positiveVisitor = new TopChecker();
		negativeVisitor = new BottomChecker();
	}
	
		
//	public void setExternalSignature(Set<OWLEntity> signature){
//		externalSignature = signature;
//	}
	
	
	
	public LocalityInfo isLocalAxiom(OWLAxiom axiom, Set<OWLEntity> extSignature, Set<OWLEntity> globalEnts){
		externalSignature = extSignature;
		globalEntities = globalEnts;
		axiom.accept(this);
		return new LocalityInfo(isLocal, canMakeLocal, solutions);
		//all three variables canMakeLocal, isLocal and solutions are updated every time an axiom is visited
	}
		
	protected LocalityInfo isBottomClass(OWLClassExpression exp) {
		exp.accept(negativeVisitor);
		return negativeVisitor.info();
	}
	
	protected LocalityInfo isTopClass(OWLClassExpression exp) {
		exp.accept(positiveVisitor);
		return positiveVisitor.info();
	}
		
	
	
	
	/*
	 * ------------------------------------------------
	 * CLASS AXIOMS
	 * -------------------------------------------------
	 * 
	 */
	
	public void visit(OWLSubClassOfAxiom axiom) {
		//An OWLSubClassOfAxiom is bot-local if the subclass is locally bottom or the superclass is locally top
		LocalityInfo bottomInfo = isBottomClass(axiom.getSubClass());
		LocalityInfo topInfo = isTopClass(axiom.getSuperClass());
		isLocal = bottomInfo.is() || topInfo.is();
    	if (isLocal){
    		canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();			
		}
		else{
			canMakeLocal = false;
			solutions = new LinkedList<Set<OWLEntity>>();
			if (bottomInfo.canMake()){
				canMakeLocal = true;
				solutions.addAll(bottomInfo.getSolutions());
			}
			if (topInfo.canMake()){
				canMakeLocal = true;
				solutions.addAll(topInfo.getSolutions());
			}
		}
    }

	
    public void visit(OWLDisjointClassesAxiom axiom) {
    	//An OWLDisjointClassesAxiom is bot-local if at most one of the involved class expressions is not locally negative.";
    	List<OWLClassExpression> classExps = axiom.getClassExpressionsAsList();
     	List<List<Set<OWLEntity>>> sols = new LinkedList<List<Set<OWLEntity>>>();
    	
    	ListProcessor listProc = new ListProcessor();
    	int nAlreadyBott = 0;
    	int nCanBeBott = 0;
    	int nExps = classExps.size();
    	LocalityInfo locInfo;
    	for (OWLClassExpression exp : classExps){
    		locInfo = isBottomClass(exp);
    		if (locInfo.is()){
    			nCanBeBott++;
    			nAlreadyBott++;
    		}
    		else{
    			if (locInfo.canMake()){
    				nCanBeBott++;
   					sols.add(locInfo.getSolutions());
    			}
    		}    		
    	}
    	
    	solutions = new LinkedList<Set<OWLEntity>>();
    	
    	if (nAlreadyBott > nExps-2){
    		isLocal = true;
    		canMakeLocal = true;
    	}
    	else{
    		isLocal =  false;
    		if (nCanBeBott < nExps-1){
        		canMakeLocal = false;
        	}
    		else{
    			if (nCanBeBott < nExps){
    				canMakeLocal = true;
    				solutions = listProc.getAllCombinations(sols, true); //true because we want solutions containing one of the solutions for each disjunct
    			}
    			else{
    				canMakeLocal = true;
    				solutions = listProc.getAllCombinations(sols, false); //false because we want solutions containing one of the solutions for all but one of the disjuncts
    			}
    		}
    	}
    }	


    public void visit(OWLEquivalentClassesAxiom axiom) {
		//An OWLEquivalentClassesAxiom is local if all the classes asserted to be equivalent are locally positive or locally negative - all the same
    	ListProcessor listProc = new ListProcessor();
		LocalityInfo posInfo;
		LocalityInfo negInfo;
		
		boolean atLeastOneNotBottom = false;
		boolean atLeastOneNotTop = false;
		boolean cantMakeAllBottom = false;
		boolean cantMakeAllTop = false;
		List<List<Set<OWLEntity>>> solsForBottom = new LinkedList<List<Set<OWLEntity>>>();	
		List<List<Set<OWLEntity>>> solsForTop = new LinkedList<List<Set<OWLEntity>>>();
		
		for (OWLClassExpression exp : axiom.getClassExpressions()){
			if (!cantMakeAllBottom){
				negInfo = isBottomClass(exp);
				if (!negInfo.is()){
					atLeastOneNotBottom = true;
					if (negInfo.canMake()){
						solsForBottom.add(negInfo.getSolutions()); 
					}
					else cantMakeAllBottom = true;
				}	
			}
			if (!cantMakeAllTop){
				posInfo = isTopClass(exp);
				if (!posInfo.is()){
					atLeastOneNotTop = true;
					if (posInfo.canMake()){
						solsForTop.add(posInfo.getSolutions()); 
					}
					else cantMakeAllTop = true;
				}
			}
		}
		isLocal = !(atLeastOneNotBottom && atLeastOneNotTop);
		canMakeLocal = !(cantMakeAllBottom && cantMakeAllTop);
		solutions = new LinkedList<Set<OWLEntity>>();
		if (canMakeLocal && !isLocal){
			if (!cantMakeAllBottom){
				solutions.addAll(listProc.getAllCombinations(solsForBottom, true));
			}
			if (!cantMakeAllTop){
				solutions.addAll(listProc.getAllCombinations(solsForTop, true));
			}	
		}
    }
		
		
    public void visit(OWLDisjointUnionAxiom axiom) {
    	//An OWLDisjointUnionAxiom is bot-local if the defined class and all the disjunct are locally negative
    	LocalityInfo locInfo = isBottomClass(axiom.getOWLClass());
		isLocal = locInfo.is();
		canMakeLocal = locInfo.canMake();
		List<List<Set<OWLEntity>>> solsForBottom = new LinkedList<List<Set<OWLEntity>>>();
		solsForBottom.add(locInfo.getSolutions());
		for (OWLClassExpression classExp : axiom.getClassExpressions()){
			locInfo = isBottomClass(classExp);
			isLocal = isLocal && locInfo.is();
			canMakeLocal = canMakeLocal && locInfo.canMake();
    		solsForBottom.add(locInfo.getSolutions());
    	}
    	if (isLocal || !canMakeLocal){
    		solutions = new LinkedList<Set<OWLEntity>>();
    	}
    	else{
    		ListProcessor listProc = new ListProcessor();
    		solutions =  listProc.getAllCombinations(solsForBottom, true);	
    	}
    }
    
	///END CLASS AXIOMS
	
	
        
    
	/*
	 * -----------------------------------------
	 * PROPERTY AXIOMS
	 * -----------------------------------------
	 * 
	 */
	
	public void visit(OWLSubObjectPropertyOfAxiom axiom) {
		//An OWLSubObjectPropertyOfAxiom is bot-local iff the subproperty does not belong to the external signature
		OWLObjectProperty prop = axiom.getSubProperty().getNamedProperty();//whether the property is anonymous or not, to make it bottom it is enough to make bottom the named proprety used to construct it 
		solutions = new LinkedList<Set<OWLEntity>>();
		canMakeLocal = true;
		if (!externalSignature.contains(prop)){
			isLocal = true;
		}
		else{
			isLocal = false;
			if (globalEntities.contains(prop)){
				canMakeLocal = false;
			}
			else{
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);				
			}
		}
	}
	
	
	public void visit(OWLSubDataPropertyOfAxiom axiom) {
		//An OWLSubDataPropertyOfAxiom is bot-local iff the subproperty does not belong to the external signature
		OWLDataProperty prop = axiom.getSubProperty().asOWLDataProperty();
		solutions = new LinkedList<Set<OWLEntity>>();
		canMakeLocal = true;
		if (!externalSignature.contains(prop)){
			isLocal = true;
		}
		else{
			isLocal = false;
			if (globalEntities.contains(prop)){
				canMakeLocal = false;
			}
			else{
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);				
			}
		}			
	}
	
	
	public void visit(OWLEquivalentObjectPropertiesAxiom axiom) {
		//An OWLEquivalentObjectPropertiesAxiom is bot-local if only properties outside the external signature are involved
		isLocal = true;
		canMakeLocal = true;
		solutions = new LinkedList<Set<OWLEntity>>();
		Set<OWLEntity> auxSet = new HashSet<OWLEntity>();
		OWLObjectProperty aux;
		for(OWLObjectPropertyExpression objPropExp : axiom.getProperties()) {
			aux = objPropExp.getNamedProperty();
			if (externalSignature.contains(aux)){
				isLocal=false;
				if (globalEntities.contains(aux))
					canMakeLocal = false;
				else
					auxSet.add(aux);
			}
		}
		if (canMakeLocal)
			solutions.add(auxSet);			
	}
	
	
	public void visit(OWLEquivalentDataPropertiesAxiom axiom) {
		//An OWLEquivalentDataPropertiesAxiom is bot-local if only properties outside the external signature are involved
		isLocal = true;
		canMakeLocal = true;
		solutions = new LinkedList<Set<OWLEntity>>();
		Set<OWLEntity> auxSet = new HashSet<OWLEntity>();
		OWLDataProperty aux;
		for(OWLDataPropertyExpression dataPropExp : axiom.getProperties()) {
			aux = dataPropExp.asOWLDataProperty();
			if (externalSignature.contains(aux)){
				isLocal=false;
				if (globalEntities.contains(aux))
					canMakeLocal = false;
				else
					auxSet.add(aux);
			}
		}
		if (canMakeLocal)
			solutions.add(auxSet);			
		}

	
	public void visit(OWLDisjointDataPropertiesAxiom axiom) {
		//An OWLDisjointDataPropertiesAxiom is bot-local if at most one of the involved properties is not locally negative.";
		Set<OWLDataProperty> externalProps = new HashSet<OWLDataProperty>();
    	for (OWLDataPropertyExpression prop : axiom.getProperties()){
    		if (externalSignature.contains(prop.asOWLDataProperty())){
    			externalProps.add(prop.asOWLDataProperty());
    		}
    	}
    	
    	isLocal = true;
    	canMakeLocal = true;
    	solutions = new LinkedList<Set<OWLEntity>>();
    	
    	if (externalProps.size() > 1){
    		isLocal = false;
    		
    		Set<OWLEntity> globalProps = new HashSet<OWLEntity>();
    		for (OWLDataProperty prop : externalProps)
    			if (globalEntities.contains(prop))
    				globalProps.add(prop);
    			
    		Set<OWLEntity> auxSet;
    		switch(globalProps.size()){
    		case 0:
    			for (OWLDataProperty prop : externalProps){
    				auxSet = new HashSet<OWLEntity>();
    				auxSet.addAll(externalProps);
    				auxSet.remove(prop);
            		solutions.add(auxSet);	
        		}
    			break;
    		case 1:
    			for (OWLEntity prop : globalProps){//just the one!
        			auxSet = new HashSet<OWLEntity>();
            		auxSet.addAll(externalProps);
            		auxSet.remove(prop);
            		solutions.add(auxSet);	
        		}
    			break;
    		default:
    			canMakeLocal = false;
    		}
    	}
	}
	
	
	public void visit(OWLDisjointObjectPropertiesAxiom axiom) {
		//An OWLDisjointDataPropertiesAxiom is local if at most one of the involved properties is not locally negative.";
		Set<OWLObjectProperty> externalProps = new HashSet<OWLObjectProperty>();
    	for (OWLObjectPropertyExpression prop : axiom.getProperties()){
    		if (externalSignature.contains(prop.getNamedProperty())){
    			externalProps.add(prop.getNamedProperty());
    		}
    	}
    	
    	isLocal = true;
    	canMakeLocal = true;
    	solutions = new LinkedList<Set<OWLEntity>>();
    	
    	if (externalProps.size() > 1){
    		isLocal = false;
    		
    		Set<OWLEntity> globalProps = new HashSet<OWLEntity>();
    		for (OWLObjectProperty prop : externalProps)
    			if (globalEntities.contains(prop))
    				globalProps.add(prop);
    			
    		Set<OWLEntity> auxSet;
    		switch(globalProps.size()){
    		case 0:
    			for (OWLObjectProperty prop : externalProps){
    				auxSet = new HashSet<OWLEntity>();
    				auxSet.addAll(externalProps);
    				auxSet.remove(prop);
            		solutions.add(auxSet);	
        		}
    			break;
    		case 1:
    			for (OWLEntity prop : globalProps){//just the one!
        			auxSet = new HashSet<OWLEntity>();
            		auxSet.addAll(externalProps);
            		auxSet.remove(prop);
            		solutions.add(auxSet);	
        		}
    			break;
    		default:
    			canMakeLocal = false;
    		}
    	}
	}

	
	public void visit(OWLFunctionalDataPropertyAxiom axiom) {
		//An OWLFunctionalDataPropertyAxiom axiom is bot-local iff property does not belong to the external signature
		OWLDataProperty prop = axiom.getProperty().asOWLDataProperty();
		isLocal = true;
		canMakeLocal = true;
		solutions = new LinkedList<Set<OWLEntity>>();
		if (externalSignature.contains(prop)){
			isLocal = false;
			if (globalEntities.contains(prop))
				canMakeLocal = false;
			else{
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);	
			}
		}
	}

	
	public void visit(OWLFunctionalObjectPropertyAxiom axiom) {
		//An OWLFunctionalObjectPropertyAxiom axiom is bot-local iff property does not belong to the external signature
		OWLObjectProperty prop = axiom.getProperty().getNamedProperty();
		canMakeLocal = true;
		solutions = new LinkedList<Set<OWLEntity>>();
		isLocal = true;
		if (externalSignature.contains(prop)){
			isLocal = false;
			if (globalEntities.contains(prop))
				canMakeLocal = false;
			else{
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);	
			}
		}
	}


	public void visit(OWLInverseFunctionalObjectPropertyAxiom axiom) {
		//An OWLInverseFunctionalObjectPropertyAxiom axiom is bot-local iff property does not belong to the external signature
		OWLObjectProperty prop = axiom.getProperty().getNamedProperty();
		isLocal = true;
		canMakeLocal = true;
		solutions = new LinkedList<Set<OWLEntity>>();
		if (externalSignature.contains(prop)){
			isLocal = false;
			if (globalEntities.contains(prop))
				canMakeLocal = false;
			else{
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);	
			}
		}
	}

	
	public void visit(OWLInverseObjectPropertiesAxiom axiom) {
		//An OWLInverseObjectPropertiesAxiom axiom is bot-local iff both involved properties do not belong to the external signature
		OWLObjectProperty prop1 = axiom.getFirstProperty().getNamedProperty();
		OWLObjectProperty prop2 = axiom.getSecondProperty().getNamedProperty();
		
		boolean b1 = externalSignature.contains(prop1);
		boolean b2 = externalSignature.contains(prop2);
		
		isLocal = !(b1 || b2);
		canMakeLocal = true;
		solutions = new LinkedList<Set<OWLEntity>>();
		
		if (!isLocal){
			Set<OWLEntity> aux = new HashSet<OWLEntity>();
			if (b1){
				if (globalEntities.contains(prop1))
					canMakeLocal = false;
				else
					aux.add(prop1);	
			}
			if (b2){
				if (globalEntities.contains(prop2))
					canMakeLocal = false;
				else
					aux.add(prop2);	
			}
			if (canMakeLocal)
				solutions.add(aux);
		}
	}

	
	public void visit(OWLIrreflexiveObjectPropertyAxiom axiom) {
		//An OWLIrreflexiveObjectPropertyAxiom axiom is bottom-local iff property does not belong to the external signature
		OWLObjectProperty prop = axiom.getProperty().getNamedProperty();
		isLocal = true;
		canMakeLocal = true;
		solutions = new LinkedList<Set<OWLEntity>>();
		if (externalSignature.contains(prop)){
			isLocal = false;
			if (globalEntities.contains(prop))
				canMakeLocal = false;
			else{
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);
			}
		}
	}

	
	public void visit(OWLAsymmetricObjectPropertyAxiom axiom) {
		//An OWLAsymmetricObjectPropertyAxiom axiom is bot-local iff property does not belong to the external signature
		OWLObjectProperty prop = axiom.getProperty().getNamedProperty();
		isLocal = true;
		canMakeLocal = true;
		solutions = new LinkedList<Set<OWLEntity>>();
		if (externalSignature.contains(prop)){
			isLocal = false;
			if (globalEntities.contains(prop))
				canMakeLocal = false;
			else{
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);
			}
		}
	}
	
	
	public void visit(OWLReflexiveObjectPropertyAxiom axiom) {
		//An OWLSymmetricObjectPropertyAxiom axiom is bot-local iff property does not belong to the external signature
		//Or should it always be non local? It is always non-local in the OWLAPI
		OWLObjectProperty prop = axiom.getProperty().getNamedProperty();
		isLocal = true;
		canMakeLocal = true;
		solutions = new LinkedList<Set<OWLEntity>>();
		if (externalSignature.contains(prop)){
			isLocal = false;
			if (globalEntities.contains(prop))
				canMakeLocal = false;
			else{
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);
			}
		}
	}
	
	
	public void visit(OWLSymmetricObjectPropertyAxiom axiom) {
		//An OWLSymmetricObjectPropertyAxiom axiom is bot-local iff property does not belong to the external signature
		OWLObjectProperty prop = axiom.getProperty().getNamedProperty();
		isLocal = true;
		canMakeLocal = true;
		solutions = new LinkedList<Set<OWLEntity>>();
		if (externalSignature.contains(prop)){
			isLocal = false;
			if (globalEntities.contains(prop))
				canMakeLocal = false;
			else{
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);
			}
		}
	}

	
	public void visit(OWLTransitiveObjectPropertyAxiom axiom) {
		//An OWLFunctionalObjectPropertyAxiom axiom is bot-local iff property does not belong to the external signature
		OWLObjectProperty prop = axiom.getProperty().getNamedProperty();
		isLocal = true;
		canMakeLocal = true;
		solutions = new LinkedList<Set<OWLEntity>>();
		if (externalSignature.contains(prop)){
			isLocal = false;
			if (globalEntities.contains(prop))
				canMakeLocal = false;
			else{
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);
			}
		}
	}

	
	public void visit(OWLObjectPropertyDomainAxiom axiom) {
		//An OWLObjectPropertyDomainAxiom is bot-local iff the property does not belong to the external signature or the domain is locally top
		isLocal = false;
		canMakeLocal = true;
		solutions = new LinkedList<Set<OWLEntity>>();

		LocalityInfo locInfo = isTopClass(axiom.getDomain());
		if (locInfo.is()){
			isLocal = true;
		}
		else{
			if (locInfo.canMake()){
				solutions.addAll(locInfo.getSolutions());
			}
		}
		
		if (!isLocal){
			OWLObjectProperty prop = axiom.getProperty().getNamedProperty();
			if (!externalSignature.contains(prop)){
				isLocal = true;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
			else{
				if (globalEntities.contains(prop))
					canMakeLocal = locInfo.canMake();
				else{
					Set<OWLEntity> aux = new HashSet<OWLEntity>();
					aux.add(prop);
					solutions.add(aux);
				}
			}
		}
	}

	
	public void visit(OWLDataPropertyDomainAxiom axiom) {
		//An OWLDataPropertyDomainAxiom is bot-local iff the property does not belong to the external signature or the domain is locally top
		isLocal = false;
		canMakeLocal = true; //ultimately we can always make this axiom local by removing the property from the externalSignature
		solutions = new LinkedList<Set<OWLEntity>>();

		LocalityInfo locInfo = isTopClass(axiom.getDomain());
		if (locInfo.is()){
			isLocal = true;
		}
		else{
			if (locInfo.canMake()){
				solutions.addAll(locInfo.getSolutions());
			}
		}
		
		if (!isLocal){
			OWLDataProperty prop = axiom.getProperty().asOWLDataProperty();
			if (!externalSignature.contains(prop)){
				isLocal = true;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
			else{
				if (globalEntities.contains(prop))
					canMakeLocal = locInfo.canMake();
				else{
					Set<OWLEntity> aux = new HashSet<OWLEntity>();
					aux.add(prop);
					solutions.add(aux);
				}
			}
		}
	}

	
	public void visit(OWLObjectPropertyRangeAxiom axiom) {
		//An OWLObjectPropertyRangeAxiom is bot-local iff the property does not belong to the external signature or the range is locally positive
		isLocal = false;
		canMakeLocal = true;
		solutions = new LinkedList<Set<OWLEntity>>();

		LocalityInfo locInfo = isTopClass(axiom.getRange());
		if (locInfo.is()){
			isLocal = true;
		}
		else{
			if (locInfo.canMake()){
				solutions.addAll(locInfo.getSolutions());
			}
		}
		
		if (!isLocal){
			OWLObjectProperty prop = axiom.getProperty().getNamedProperty();
			if (!externalSignature.contains(prop)){
				isLocal = true;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
			else{
				if (globalEntities.contains(prop))
					canMakeLocal = locInfo.canMake();
				else{
					Set<OWLEntity> aux = new HashSet<OWLEntity>();
					aux.add(prop);
					solutions.add(aux);
				}
			}
		}
	}

	
	public void visit(OWLDataPropertyRangeAxiom axiom) {	
		//An OWLDataPropertyRangeAxiom is bottom-local iff the property does not belong to the external signature - the range can never be locally negative because it's a datatype, not a class
		OWLDataProperty prop = axiom.getProperty().asOWLDataProperty();
		canMakeLocal = true;
		solutions = new LinkedList<Set<OWLEntity>>();
		
		if (!externalSignature.contains(prop)){
			isLocal = true;
		}
		else{
			if (globalEntities.contains(prop))
				canMakeLocal = false;
			else{
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);
			}
		}
	}
	

	public void visit(OWLSubPropertyChainOfAxiom axiom) {
		//An OWLSubPropertyChainOfAxiom axiom is bot-local iff at least one of the properties in the chain does not belong to the external signature
		isLocal = false;
		canMakeLocal = true;
		solutions = new LinkedList<Set<OWLEntity>>();
		
//		OWLEntity aux;
		Set<OWLEntity> auxSet;
		
		Set<OWLObjectProperty> props = axiom.getObjectPropertiesInSignature();
		props.removeAll(globalEntities);
		if (props.isEmpty())
			canMakeLocal = false;
		for (OWLObjectProperty prop : props){
			if (!externalSignature.contains(prop)){
				isLocal = true;
				solutions = new LinkedList<Set<OWLEntity>>();
				return;
			}
			else{
				auxSet = new HashSet<OWLEntity>();
				auxSet.add(prop);
				solutions.add(auxSet);
			}
		}
	}

	
	//End Property Axioms
	//---------------------------------------------------------------

	
	
	/*
	 * OTHERS
	 */
	
	public void visit(OWLDeclarationAxiom axiom) {
		//An OWLDeclarationAxiom is bot-local iff the declared entity does not belong to the foreign signature
		OWLEntity ent = axiom.getEntity();
		canMakeLocal = true;
		solutions = new LinkedList<Set<OWLEntity>>();
		if (!externalSignature.contains(ent)){
			isLocal = true;
		}
		else{
			isLocal = false;
			if (globalEntities.contains(ent))
				canMakeLocal = false;
			else{
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(ent);
				solutions.add(aux);				
			}
		}
	}
	
	
	public void visit(SWRLRule axiom) {
		//Currently, a SWRLRule axiom is always considered not bottom-local
		isLocal = false;
		canMakeLocal = false;
		solutions = new LinkedList<Set<OWLEntity>>();
	}
	
	
	public void visit(OWLHasKeyAxiom axiom){
		//Currently, a HasKey axiom is always considered not bottom-local
		isLocal = false;
		canMakeLocal = false;
		solutions = new LinkedList<Set<OWLEntity>>();
	}

	
	public void visit(OWLDatatypeDefinitionAxiom axiom){
		//Currently, a OWLDatatypeDefinition axiom is always considered non-local
		isLocal = false;
		canMakeLocal = false;
		solutions = new LinkedList<Set<OWLEntity>>();
	}   
	
	
	
	/*
	 * ------------------------------------------------
	 * ASSERTION AXIOMS - we don't really care about these, since we eliminate this kind of axiom from the start
	 * -------------------------------------------------
	 * 
	 */
	
	public void visit(OWLClassAssertionAxiom axiom) {}
	
	
	public void visit(OWLNegativeDataPropertyAssertionAxiom axiom) {}
	
	
	public void visit(OWLNegativeObjectPropertyAssertionAxiom axiom) {}

	
	public void visit(OWLObjectPropertyAssertionAxiom axiom) {}

	
	public void visit(OWLDataPropertyAssertionAxiom axiom) {}
	
	
	public void visit(OWLSameIndividualAxiom axiom) {}
	
	
	public void visit(OWLDifferentIndividualsAxiom axiom) {}
	
	/*End Assertion Axioms*/
	//------------------------------------------------------------------------

	
	/*
	 * ----------------------
	 * ANNOTATION AXIOMS - useless for classification, we already removed them when first loading the ontology
	 * ----------------------
	 */
		
	public void visit(OWLAnnotationAssertionAxiom axiom){}
	
	
	public void visit(OWLSubAnnotationPropertyOfAxiom axiom){}
	
	
	public void visit(OWLAnnotationPropertyDomainAxiom axiom){}
	
	
	public void visit(OWLAnnotationPropertyRangeAxiom axiom){}
	
	/*END ANNOTATIONS
	 ------------------------------------*/
	
	
	 
		
	//----------------------------
	
	private class BottomChecker implements
	OWLClassExpressionVisitor {
		
		public boolean isBottom;
		public boolean canMakeBottom;
		public List<Set<OWLEntity>> solutions; //solutions will NEVER contain a set whose intersection with the externalSignature is nonempty
		
		
		public LocalityInfo info(){
			return new LocalityInfo(isBottom, canMakeBottom, solutions);
		}
		

		
		public void visit(OWLClass exp) {
			//An OWLClass concept is locally bottom wrt a signature iff the concept is not in that signature
			if (exp.isOWLThing() || globalEntities.contains(exp)){
				isBottom = false;
				canMakeBottom = false;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
			else{
				canMakeBottom = true;
				solutions = new LinkedList<Set<OWLEntity>>();
				if (externalSignature.contains(exp)){
					isBottom = false;
					Set<OWLEntity> aux = new HashSet<OWLEntity>();
					aux.add(exp);
					solutions.add(aux);
				}
				else
					isBottom = true;
			}
		}


		public void visit(OWLObjectIntersectionOf exp) {
			//An OWLObjectIntersectionOf concept is locally negative if at least one conjunct is locally negative
			isBottom = false;
			boolean canBoolAcc = false;
			List<Set<OWLEntity>> auxList = new LinkedList<Set<OWLEntity>>();
			Iterator<OWLClassExpression> iterator = exp.asConjunctSet().iterator();
			OWLClassExpression conjunct;
			
			while (iterator.hasNext() && !isBottom){
				conjunct = iterator.next();
				conjunct.accept(this);
				if (!isBottom && canMakeBottom){
					auxList.addAll(solutions);
					canBoolAcc = true;
				}
			}
			
			canMakeBottom = canBoolAcc || isBottom;
			
			if (!isBottom && canMakeBottom)
				solutions = auxList;
			else
				solutions = new LinkedList<Set<OWLEntity>>();			
		}


		public void visit(OWLObjectUnionOf exp) {
			//An OWLObjectUnionOf concept is locally negative iff all disjuncts are locally negative
	    	LocalityInfo locInfo;
	    	isLocal = true;
	    	canMakeLocal = true;
			List<List<Set<OWLEntity>>> solsForBottom = new LinkedList<List<Set<OWLEntity>>>();
			for (OWLClassExpression classExp : exp.getOperands()){
				locInfo = isBottomClass(classExp);
				isLocal = isLocal && locInfo.is();
				canMakeLocal = canMakeLocal && locInfo.canMake();
	    		solsForBottom.add(locInfo.getSolutions());
	    	}
	    	if (isLocal || !canMakeLocal)
	    		solutions = new LinkedList<Set<OWLEntity>>();
	    	else{
	    		ListProcessor listProc = new ListProcessor();
	    		solutions =  listProc.getAllCombinations(solsForBottom, true);	
	    	}				
		}

		
		public void visit(OWLObjectComplementOf exp) {
			//An OWLObjectComplementOf concept is locally negative iff the negated concept is locally positive
			exp.getOperand().accept(positiveVisitor);
			LocalityInfo locInfo = positiveVisitor.info();
			
			isBottom = locInfo.is();
			canMakeBottom = locInfo.canMake();
			solutions = locInfo.getSolutions();
		}

		
		@Override
		public void visit(OWLObjectOneOf exp) {
			//An OWLObjectOneOf concept is never locally negative
			isBottom = false;
			canMakeBottom = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}


		public void visit(OWLObjectAllValuesFrom exp) {
			//An OWLObjectAllValuesFrom concept is never locally negative
			isBottom = false;
			canMakeBottom = false;
			solutions = new LinkedList<Set<OWLEntity>>(); 
		}


		public void visit(OWLDataAllValuesFrom exp) {
			//An OWLDataAllValuesFrom concept is never locally negative
			isBottom = false;
			canMakeBottom = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}


		public void visit(OWLObjectSomeValuesFrom exp) {
			//An OWLObjectSomeValuesFrom concept is locally negative iff the property or the concept is locally negative
			exp.getFiller().accept(this);
			if (!isBottom){
				OWLObjectProperty prop =  exp.getProperty().getNamedProperty();
		    	if (!externalSignature.contains(prop)){
		    		isBottom = true;
		    		canMakeBottom = true;
		    		solutions = new LinkedList<Set<OWLEntity>>();
		    	}
		    	else
		    		if (!globalEntities.contains(prop)){
		    			canMakeBottom = true; 
		    			Set<OWLEntity> aux = new HashSet<OWLEntity>();
		    			aux.add(prop);
		    			solutions.add(aux);
		    		}
			}
		}


		public void visit(OWLDataSomeValuesFrom exp) {
			//An OWLDataSomeValuesFrom concept is locally negative iff the property is locally negative
			OWLDataProperty prop =  exp.getProperty().asOWLDataProperty();
			canMakeBottom = true;
			solutions = new LinkedList<Set<OWLEntity>>();
	    	if (!externalSignature.contains(prop))
	    		isBottom = true;
	    	else{
	    		isBottom = false;
	    		if (globalEntities.contains(prop))
	    			canMakeBottom = false;
	    		else{
	    			Set<OWLEntity> aux = new HashSet<OWLEntity>();
		    		aux.add(prop);
		    		solutions.add(aux);	
	    		}
	    	}
		}

		
		public void visit(OWLObjectHasSelf exp) {
			//An OWLObjectHasSelf concept is locally negative iff the property is locally negative
			canMakeBottom = true;
			solutions = new LinkedList<Set<OWLEntity>>();

			OWLObjectProperty prop = exp.getProperty().getNamedProperty();
	
			if (!externalSignature.contains(prop))
				isBottom = true;
			else{
				isBottom = false;
				if (globalEntities.contains(prop))
	    			canMakeBottom = false;
	    		else{
	    			Set<OWLEntity> auxSet = new HashSet<OWLEntity>();
	    			auxSet.add(prop);
	    			solutions.add(auxSet);
	    		}
			}
		}


		public void visit(OWLObjectHasValue exp) {
			//An OWLObjectHasValue concept is locally negative iff the property is locally negative - it's not possible to interpret an individual as bottom
			canMakeBottom = true;
			solutions = new LinkedList<Set<OWLEntity>>();
			
			OWLObjectProperty prop = exp.getProperty().getNamedProperty();
			
			if (!externalSignature.contains(prop))
				isBottom = true;
			else{
				isBottom = false;
				if (globalEntities.contains(prop))
	    			canMakeBottom = false;
	    		else{
	    			Set<OWLEntity> auxSet = new HashSet<OWLEntity>();
	    			auxSet.add(prop);
	    			solutions.add(auxSet);
	    		}
			}
		}


		public void visit(OWLDataHasValue exp) {
			//An OWLObjectHasValue concept is locally negative iff the property is locally negative
			canMakeBottom = true;
			solutions = new LinkedList<Set<OWLEntity>>();
			
			OWLDataProperty prop = exp.getProperty().asOWLDataProperty();
			
			if (!externalSignature.contains(prop))
				isBottom = true;
			else{
				isBottom = false;
				if (globalEntities.contains(prop))
	    			canMakeBottom = false;
	    		else{
	    			Set<OWLEntity> auxSet = new HashSet<OWLEntity>();
	    			auxSet.add(prop);
	    			solutions.add(auxSet);
	    		}
			}
		}

    
		public void visit(OWLObjectMinCardinality exp) {
			//An OWLObjectMinCardinality concept is locally negative iff the property or the filler are locally negative
			exp.getFiller().accept(this);
			if (!isBottom){
				OWLObjectProperty prop = exp.getProperty().getNamedProperty();
				if (externalSignature.contains(prop)){
					if (!globalEntities.contains(prop)){
						canMakeBottom = true;
						Set<OWLEntity> aux = new HashSet<OWLEntity>();
						aux.add(prop);
						solutions.add(aux);
					}
				}
				else{
					canMakeBottom = true;
					isBottom = true;
					solutions = new LinkedList<Set<OWLEntity>>();
				}
			}
		}


		public void visit(OWLDataMinCardinality exp) {
			//An OWLDataMinCardinality concept is locally negative iff the property is locally negative
			canMakeBottom = true;
			solutions = new LinkedList<Set<OWLEntity>>();
			OWLDataProperty prop = exp.getProperty().asOWLDataProperty();
			if (externalSignature.contains(prop)){
				isBottom = false;				
				if (globalEntities.contains(prop))
					canMakeBottom = false;
				else{
					Set<OWLEntity> aux = new HashSet<OWLEntity>();
		    		aux.add(prop);
					solutions.add(aux);	
				}
	    	}
			else
				isBottom = true;				
		}


		public void visit(OWLObjectMaxCardinality exp) {
			//An OWLObjectMaxCardinality concept is never locally negative
			isBottom = false;
			canMakeBottom = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}


		public void visit(OWLDataMaxCardinality exp) {
			//An OWLDataMaxCardinality concept is never locally negative
			isBottom = false;
			canMakeBottom = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

		
		public void visit(OWLObjectExactCardinality exp) {
			//An OWLObjectMinCardinality concept is locally negative iff the property (or the filler, if it's qualified) is locally negative
			exp.getFiller().accept(this);
			if (!isBottom){
				OWLObjectProperty prop = exp.getProperty().getNamedProperty();
				if (externalSignature.contains(prop)){
					if (!globalEntities.contains(prop)){
						canMakeBottom = true;
						Set<OWLEntity> aux = new HashSet<OWLEntity>();
						aux.add(prop);
						solutions.add(aux);
					}
				}
				else{
					isBottom = true;
					canMakeBottom = true;
					solutions = new LinkedList<Set<OWLEntity>>();
				}
			}
		}


		public void visit(OWLDataExactCardinality exp){
			//An OWLDataExactCardinality concept is locally negative iff the property is locally negative
			OWLDataProperty prop = exp.getProperty().asOWLDataProperty();
			canMakeBottom = true;
			solutions = new LinkedList<Set<OWLEntity>>();
			if (externalSignature.contains(prop)){
				isBottom = false;
				if (globalEntities.contains(prop))
					canMakeBottom = false;
				else{
					Set<OWLEntity> aux = new HashSet<OWLEntity>();
					aux.add(exp.getProperty().asOWLDataProperty());
					solutions.add(aux);					
				}
			}
			else
				isBottom = true;
		}

	}
	
	
	
	
	
	//--------------------------------
	
	
	public class TopChecker implements
	OWLClassExpressionVisitor {

		public boolean isTop;
		public boolean canMakeTop;
		public List<Set<OWLEntity>> solutions;//solutions will NEVER contain a set whose intersection with the externalSignature is nonempty
		
		
		public LocalityInfo info(){
			return new LocalityInfo(isTop, canMakeTop, solutions);
		}

		
		public void visit(OWLClass exp) { //checked
			//An OWLClass is never locally top unless it's top
			isTop = exp.isOWLThing();
			canMakeTop = isTop;
			solutions = new LinkedList<Set<OWLEntity>>();			
		}


		public void visit(OWLObjectIntersectionOf exp) {
			//An OWLObjectIntersection concept is locally positive iff all the operands are locally positive
			LocalityInfo locInfo;
	    	isTop = true;
	    	canMakeTop = true;
			List<List<Set<OWLEntity>>> solsForTop = new LinkedList<List<Set<OWLEntity>>>();
			for (OWLClassExpression classExp : exp.getOperands()){
				locInfo = isTopClass(classExp);
				isTop = isTop && locInfo.is();
				canMakeTop = canMakeTop && locInfo.canMake();
	    		solsForTop.add(locInfo.getSolutions());
	    	}
	    	if (isTop || !canMakeTop)
	    		solutions = new LinkedList<Set<OWLEntity>>();
	    	else{
	    		ListProcessor listProc = new ListProcessor();
	    		solutions =  listProc.getAllCombinations(solsForTop, true);	
	    	}
		}


		public void visit(OWLObjectUnionOf exp) {
			//An OWLObjectIntersection concept is locally positive iff at least of the operands is locally positive
			isTop = false;
			boolean canBoolAcc = false;
			List<Set<OWLEntity>> auxList = new LinkedList<Set<OWLEntity>>();
			Iterator<OWLClassExpression> iterator = exp.getOperands().iterator();
			OWLClassExpression conjunct;
			
			while (iterator.hasNext() && !isTop){
				conjunct = iterator.next();
				conjunct.accept(this);
				if (!isTop && canMakeTop){
					auxList.addAll(solutions);
					canBoolAcc = true;
				}
			}
			
			canMakeTop = canBoolAcc || isTop;
			
			if (!isTop && canMakeTop)
				solutions = auxList;
			else
				solutions = new LinkedList<Set<OWLEntity>>();
		}


		public void visit(OWLObjectComplementOf exp) {
			//An OWLObjectComplementOf concept is locally positive iff the negated concept is locally negative
			exp.getOperand().accept(negativeVisitor);
			LocalityInfo locInfo = negativeVisitor.info();
			isTop = locInfo.is();
			canMakeTop = locInfo.canMake();
			solutions = locInfo.getSolutions();
		}


		public void visit(OWLObjectOneOf exp) {
			//An OWLObjectOneOf concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}


		public void visit(OWLDataOneOf exp) {
			//An OWLDataOneOf concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
		

		public void visit(OWLObjectAllValuesFrom exp) {
			//An OWLObjectAllValueFrom concept is locally positive iff the property is locally negative or the filler is locally positive
			exp.getFiller().accept(this);
			if (!isTop){
				OWLObjectProperty prop =  exp.getProperty().getNamedProperty();
		    	if (!externalSignature.contains(prop)){
		    		isTop = true;
		    		canMakeTop = true;
		    		solutions = new LinkedList<Set<OWLEntity>>();
		    	}
		    	else{
		    		if (!globalEntities.contains(prop)){
		    			canMakeTop = true;
			    		Set<OWLEntity> aux = new HashSet<OWLEntity>();
			    		aux.add(prop);
			    		solutions.add(aux);		    			
		    		}
		    	}	
			}
		}


		public void visit(OWLDataAllValuesFrom exp) {
			//An OWLDataAllValueFrom concept is locally positive iff the property is locally negative
			OWLDataProperty prop =  exp.getProperty().asOWLDataProperty();
			canMakeTop = true;
			solutions = new LinkedList<Set<OWLEntity>>();
	    	if (!externalSignature.contains(prop))
	    		isTop = true;
	    	else{
	    		isTop = false;
	    		if (globalEntities.contains(prop))
	    			canMakeTop = false;
	    		else{
	    			Set<OWLEntity> aux = new HashSet<OWLEntity>();
		    		aux.add(prop);
		    		solutions.add(aux);	
	    		}
	    	}
		}


		public void visit(OWLObjectSomeValuesFrom exp) {
			//An OWLObjectSomeValuesFrom concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

		
		public void visit(OWLDataSomeValuesFrom exp) {
			//An OWLDataSomeValuesFrom concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

		
		public void visit(OWLObjectHasSelf exp) {
			//An OWLObjectHasSelf concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}


		public void visit(OWLObjectHasValue exp) {
			//An OWLObjectHasValue concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}


		public void visit(OWLDataHasValue exp) {
			//An OWLDataHasValue concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();		
		}
		

		public void visit(OWLObjectMinCardinality exp) {
			//An OWLObjectMinCardinality concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();		
		}

		
		public void visit(OWLDataMinCardinality exp) {
			//An OWLDataMinCardinality concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();		
		}

		
		public void visit(OWLObjectMaxCardinality exp) {		
			//An OWLObjectMaxCardinality concept is locally positive iff the property or the filler concept is locally negative
			LocalityInfo locInfo = isBottomClass(exp.getFiller());			
			isTop = locInfo.is();
    		solutions = locInfo.getSolutions();
    		canMakeTop = locInfo.canMake();
			
			if (!isTop){
				OWLObjectProperty prop =  exp.getProperty().getNamedProperty();
		    	if (!externalSignature.contains(prop)){
		    		isTop = true;
		    		canMakeTop = true;
		    		solutions = new LinkedList<Set<OWLEntity>>();
		    	}
		    	else{
		    		if (!globalEntities.contains(prop)){
		    			canMakeTop = true;
			    		Set<OWLEntity> aux = new HashSet<OWLEntity>();
			    		aux.add(prop);
			    		solutions.add(aux);		    			
		    		}
		    	}	
			}
		}


		public void visit(OWLDataMaxCardinality exp) {
			//An OWLDataMaxCardinality concept is locally positive iff the property is locally negative
			OWLDataProperty prop =  exp.getProperty().asOWLDataProperty();
			canMakeTop = true;
    		solutions = new LinkedList<Set<OWLEntity>>();
	    	if (!externalSignature.contains(prop))
	    		isTop = true;
	    	else{
	    		isTop = false;
	    		if (globalEntities.contains(prop))
	    			canMakeTop = false;
	    		else{
	    			Set<OWLEntity> aux = new HashSet<OWLEntity>();
		    		aux.add(prop);
		    		solutions.add(aux);	
	    		}
	    	}
		}	


		public void visit(OWLObjectExactCardinality desc) {
			//An OWLObjectExactCardinality concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();		
		}

		
		public void visit(OWLDataExactCardinality desc) {
			//An OWLDataExactCardinality concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

	}
	
	
}
