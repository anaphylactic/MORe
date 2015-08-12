package org.semanticweb.more.structural;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.semanticweb.HermiT.structural.OWLAxioms;
import org.semanticweb.HermiT.structural.OWLNormalization;
import org.semanticweb.more.structural.inverseRewriting.SortedGCI;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAsymmetricObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLAxiom;
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
import org.semanticweb.owlapi.model.OWLDataPropertyExpression;
import org.semanticweb.owlapi.model.OWLDataPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLDataRange;
import org.semanticweb.owlapi.model.OWLDataSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLDifferentIndividualsAxiom;
import org.semanticweb.owlapi.model.OWLDisjointDataPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentDataPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLFunctionalDataPropertyAxiom;
import org.semanticweb.owlapi.model.OWLFunctionalObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLHasKeyAxiom;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLIndividualAxiom;
import org.semanticweb.owlapi.model.OWLInverseFunctionalObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLInverseObjectPropertiesAxiom;
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
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLReflexiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLSameIndividualAxiom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubDataPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom;
import org.semanticweb.owlapi.model.OWLSymmetricObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLTransitiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.SWRLRule;

public class OWLNormalization4MORe extends OWLNormalization{

	//		/* modified version of OWLNormalization class in HermiT project
	//		 * 
	//		 * this normalizer produces axioms of the following kind:
	//		 *	
	//		 *	GCIs with 
	//		 *
	//		 *		AND_i A_i -> OR_j B_j
	//		 *
	//		 *		where each A_i is an atomic class or an existential restriction with an atomic filler
	//		 *		and each B_j is an atomic class, or a nominal expression, or an existential/universal restriction with an atomic filler, or an atMost restriction with a literal filler
	//		 *
	//		 *
	//		 *	Domain axioms are rewritten as GCIs
	//		 *	Range axioms are either rewritten as GCIs or integrated inside other GCIs 
	//		 *
	//		 *		for now only dealing with SROIQ  - no support for datatypes
	//		 *
	//		 *	Transitive properties axioms can be encoded away in GCIs, but it's optional
	//		 *
	//		 *	It seems to split A equiv {a,b,c} into A -> {a,b,c} and A(a), A(b), A(c).
	//		 *
	//		 *
	//		 *	simple ObjectProperty inclusions are kept as given
	//		 *
	//		 *	reflexive
	//		 *	irreflexive
	//		 *	symmetric
	//		 *	asymmetric
	//		 *	functional
	//		 *	disjoint
	//		 *	ObjectProperty(ies) axioms
	//		 * 
	//		 */
	//		




	protected OWLOntology o;
	protected Set<OWLAxiom> axiomsNormalizedO;
	protected Set<OWLClassExpression[]> gcis; //stop using m_axioms.conceptInclusions - in fact stop using m_axioms at all! This var is useful for DLClauses but not really for our purposes

	protected ObjectPropertyManager objectPropertyManager = new ObjectPropertyManager();
	boolean integrateRangesInRhsExistentials = false;
	boolean encodeTransitivity = false;
	boolean forInverseRewriting = false;
	Set<SortedGCI> sortedGCIs;

	

	public OWLNormalization4MORe(OWLOntology o, boolean integrateRanges, boolean encodeTransitivity, boolean forInverseRewriting) {
		super(o.getOWLOntologyManager().getOWLDataFactory(), new OWLAxioms(),0);
		this.o = o;
		this.forInverseRewriting = forInverseRewriting;
		this.encodeTransitivity = encodeTransitivity || forInverseRewriting;
			//if we are doing this for inverse rewriting then for sure we need to encode transitivity no matter what the constructor argument said
		integrateRangesInRhsExistentials = integrateRanges;
		axiomsNormalizedO = new HashSet<OWLAxiom>();
		if (forInverseRewriting)
			sortedGCIs = new HashSet<SortedGCI>();
	}

	public Set<OWLAxiom> getNormalizedOntology(){
		if (axiomsNormalizedO.isEmpty()){
			//      String ontologyIRI=o.getOntologyID().getDefaultDocumentIRI()==null ? "urn:hermit:kb" : o.getOntologyID().getDefaultDocumentIRI().toString();
			Collection<OWLOntology> importClosure=o.getImportsClosure();
			//with the mappings constructed by the AxiomVisitor, make this process them properly and then preprocess all axioms to integrate ranges
			for (OWLOntology ontology : importClosure)
				processOntology(ontology);

			List<OWLClassExpression[]> conceptInclusionsCopy = new ArrayList<OWLClassExpression[]>(m_axioms.m_conceptInclusions);
			m_axioms.m_conceptInclusions.clear();
			normalizeInclusions(objectPropertyManager.handleRangesDomainsAndTransitivity(conceptInclusionsCopy, integrateRangesInRhsExistentials, encodeTransitivity)); 
			if (!encodeTransitivity)//we cannot return the trabsitivity axioms together with the rest of axioms because the rest of axioms 
				axiomsNormalizedO.addAll(objectPropertyManager.getTransitivityAxioms());

			rearrangeClassExpressionInclusions();
		}
		return axiomsNormalizedO;
	}

	public Set<SortedGCI> getSortedGCIs(){
		if (sortedGCIs.isEmpty() && forInverseRewriting)
			getNormalizedOntology();
		return sortedGCIs;
	}


	protected void rearrangeClassExpressionInclusions(){
		NormalizedAxiomRearranger rearranger = new NormalizedAxiomRearranger();
		for (OWLClassExpression[] inclusion : m_axioms.m_conceptInclusions){
			axiomsNormalizedO.add(rearranger.rearrange(inclusion));
			if (forInverseRewriting)
				sortedGCIs.add(rearranger.getSortedGCI());
		}
	}


	@Override
	public void processOntology(OWLOntology ontology) { //I don't like this method being public but that's how it is in the OWLNormalization class in Hermit!
		//	        // Each entry in the inclusions list represents a disjunction of
		//	        // concepts -- that is, each OWLClassExpression in an entry contributes a
		//	        // disjunct. It is thus not really inclusions, but rather a disjunction
		//	        // of concepts that represents an inclusion axiom.
		//	        m_axioms.m_classes.addAll(ontology.getClassesInSignature(true));
		//	        m_axioms.m_objectProperties.addAll(ontology.getObjectPropertiesInSignature(true));
		//	        m_axioms.m_dataProperties.addAll(ontology.getDataPropertiesInSignature(true));
		//	        m_axioms.m_namedIndividuals.addAll(ontology.getIndividualsInSignature(true));
		processAxioms(ontology.getLogicalAxioms());
	}

	protected int getDefinitionsSize(){
		return m_definitions.size();
	}


	public void processAxioms(Collection<? extends OWLAxiom> axioms) {
		AxiomVisitor4MORe axiomVisitor=new AxiomVisitor4MORe();
		for (OWLAxiom axiom : axioms){
			axiom.accept(axiomVisitor);
		}
		normalizeInclusions(axiomVisitor.getClassExpressionInclusionsAsDisjunctions());
	}

	protected void normalizeInclusions(List<OWLClassExpression[]> inclusions) {
		ClassExpressionNormalizer4MORe classExpressionNormalizer=new ClassExpressionNormalizer4MORe(inclusions);
		while (!inclusions.isEmpty()) {
			OWLClassExpression simplifiedDescription=m_expressionManager.getNNF(m_expressionManager.getSimplified(m_factory.getOWLObjectUnionOf(inclusions.remove(inclusions.size()-1))));

			if (!simplifiedDescription.isOWLThing()) {
				if (simplifiedDescription instanceof OWLObjectUnionOf) {
					OWLObjectUnionOf objectOr=(OWLObjectUnionOf)simplifiedDescription;
					OWLClassExpression[] descriptions=new OWLClassExpression[objectOr.getOperands().size()];
					objectOr.getOperands().toArray(descriptions);
					if (!distributeUnionOverAnd(descriptions,inclusions) && !optimizedNegativeOneOfTranslation(descriptions,m_axioms.m_facts)) {
						for (int index=0;index<descriptions.length;index++)
							descriptions[index]=descriptions[index].accept(classExpressionNormalizer);
						m_axioms.m_conceptInclusions.add(descriptions);
					}
				}
				else if (simplifiedDescription instanceof OWLObjectIntersectionOf) {
					OWLObjectIntersectionOf objectAnd=(OWLObjectIntersectionOf)simplifiedDescription;
					for (OWLClassExpression conjunct : objectAnd.getOperands())
						inclusions.add(new OWLClassExpression[] { conjunct });
				}
				else {
					OWLClassExpression normalized=simplifiedDescription.accept(classExpressionNormalizer);
					m_axioms.m_conceptInclusions.add(new OWLClassExpression[] { normalized });
				}
			}
		}

	}
	protected boolean optimizedNegativeOneOfTranslation(OWLClassExpression[] descriptions,Collection<OWLIndividualAxiom> facts) {
		if (descriptions.length==2) {
			OWLObjectOneOf nominal=null;
			OWLClassExpression other=null;
			if (descriptions[0] instanceof OWLObjectComplementOf && ((OWLObjectComplementOf)descriptions[0]).getOperand() instanceof OWLObjectOneOf) {
				nominal=(OWLObjectOneOf)((OWLObjectComplementOf)descriptions[0]).getOperand();
				other=descriptions[1];
			}
			else if (descriptions[1] instanceof OWLObjectComplementOf && ((OWLObjectComplementOf)descriptions[1]).getOperand() instanceof OWLObjectOneOf) {
				other=descriptions[0];
				nominal=(OWLObjectOneOf)((OWLObjectComplementOf)descriptions[1]).getOperand();
			}
			if (nominal!=null && (other instanceof OWLClass || (other instanceof OWLObjectComplementOf && ((OWLObjectComplementOf)other).getOperand() instanceof OWLClass))) {
				for (OWLIndividual individual : nominal.getIndividuals())
					axiomsNormalizedO.add(m_factory.getOWLClassAssertionAxiom(other,individual));
				return true;
			}
		}
		return false;
	}


	//		@Override
	//		protected OWLClassExpression getDefinitionFor(OWLClassExpression description,boolean[] alreadyExists) {
	//			if (description instanceof OWLObjectAllValuesFrom)
	//				return getDefinitionFor(description,alreadyExists,false);
	////			else if (description instanceof OWLObjectSomeValuesFrom)
	////				return getDefinitionFor(description,alreadyExists,false);
	//			else
	//				return getDefinitionFor(description,alreadyExists,true);
	////	        return getDefinitionFor(description,alreadyExists,false);
	//	    }

	public OWLClassExpression getDefinition(OWLClassExpression description,boolean[] alreadyExists, boolean forcePositive) {
		return getDefinitionFor(description, alreadyExists, forcePositive);
	}

	public static void resetFreshClassCounter(){
		definitionsCounter = 0;
		ObjectPropertyManager.resetFreshClassCounters();
	}
	
	protected static int definitionsCounter = 0;
	protected OWLClass getFreshClass() {
//		OWLClass definition = m_factory.getOWLClass(IRI.create("internal:def#MORe"+(m_definitions.size()+m_firstReplacementIndex)));
		OWLClass definition = m_factory.getOWLClass(IRI.create("internal:def#MORe"+definitionsCounter++));
		m_definitions.put(definition,definition);
		return definition;
	}

	protected class AxiomVisitor4MORe extends AxiomVisitor {

		public AxiomVisitor4MORe() {
			super();
		}


		public List<OWLClassExpression[]> getClassExpressionInclusionsAsDisjunctions(){
			return m_classExpressionInclusionsAsDisjunctions;
		}


		public void visit(OWLSubClassOfAxiom axiom) {
			OWLClassExpression[] inclusion = new OWLClassExpression[] { negative(axiom.getSubClass()),positive(axiom.getSuperClass()) };
			m_classExpressionInclusionsAsDisjunctions.add(inclusion);
		}
		public void visit(OWLEquivalentClassesAxiom axiom) {
			if (axiom.getClassExpressions().size()>1) {
				Iterator<OWLClassExpression> iterator=axiom.getClassExpressions().iterator();
				OWLClassExpression first=iterator.next();
				OWLClassExpression last=first;
				while (iterator.hasNext()) {
					OWLClassExpression next=iterator.next();
					m_factory.getOWLSubClassOfAxiom(last, next).accept(this);
					//	                    m_classExpressionInclusionsAsDisjunctions.add(new OWLClassExpression[] { negative(last),positive(next) });
					last=next;
				}
				m_factory.getOWLSubClassOfAxiom(last, first).accept(this);
				//	                m_classExpressionInclusionsAsDisjunctions.add(new OWLClassExpression[] { negative(last),positive(first) });
			}
		}

		// Object property axioms

		public void visit(OWLSubObjectPropertyOfAxiom axiom) {

			if (!axiom.getSubProperty().isOWLBottomObjectProperty() && !axiom.getSuperProperty().isOWLTopObjectProperty()){
				axiomsNormalizedO.add(axiom);
				//no need to update sortedGCIs with this
				objectPropertyManager.registerPropertyInclusion(axiom.getSubProperty(), axiom.getSuperProperty());
			}

		}

		public void visit(OWLSubPropertyChainOfAxiom axiom) {
			List<OWLObjectPropertyExpression> subPropertyChain=axiom.getPropertyChain();
			if (!containsBottomObjectProperty(subPropertyChain) && !axiom.getSuperProperty().isOWLTopObjectProperty()) {
				OWLObjectPropertyExpression superObjectPropertyExpression=axiom.getSuperProperty().getSimplified();
				if (subPropertyChain.size()==1){
					axiomsNormalizedO.add(m_factory.getOWLSubObjectPropertyOfAxiom(subPropertyChain.get(0),superObjectPropertyExpression));
					//						addInclusion(subPropertyChain.get(0),superObjectPropertyExpression);
					//it's a normal subproperty axiom - need to add it's info to the roleHierarchy map

					objectPropertyManager.registerPropertyInclusion(subPropertyChain.get(0), superObjectPropertyExpression);

				}
				else if (subPropertyChain.size()==2 && subPropertyChain.get(0).equals(superObjectPropertyExpression) && subPropertyChain.get(1).equals(superObjectPropertyExpression))
					objectPropertyManager.registerTransitivityAxiom(m_factory.getOWLTransitiveObjectPropertyAxiom(axiom.getSuperProperty()));
				else if (subPropertyChain.size()==0)
					throw new IllegalArgumentException("Error: In OWL 2 DL, an empty property chain in property chain axioms is not allowed:" + axiom.toString());
				else {

					if (encodeTransitivity)
						throw new IllegalArgumentException("not sure transitivity encoding will work if there are complex role inclusions as well...");
					else{
						axiomsNormalizedO.add(axiom);
						objectPropertyManager.registerComplexRoleInclusion(axiom);
					}
				}
			}
		}
		public void visit(OWLReflexiveObjectPropertyAxiom axiom) {
			objectPropertyManager.registerPropertyInclusion(axiom.getProperty().getSimplified(), axiom.getProperty().getInverseProperty().getSimplified());
		}
		public void visit(OWLTransitiveObjectPropertyAxiom axiom) {
			//	            makeTransitive(axiom.getProperty());
			//	            m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(axiom.getProperty().getNamedProperty());
			objectPropertyManager.registerTransitivityAxiom(axiom);
		}
		public void visit(OWLSymmetricObjectPropertyAxiom axiom) {
			OWLObjectPropertyExpression p = axiom.getProperty().getNamedProperty();
			axiomsNormalizedO.add(m_factory.getOWLSubObjectPropertyOfAxiom(p,p.getInverseProperty()));
			objectPropertyManager.registerPropertyInclusion(p,p.getInverseProperty());
//            addInclusion(objectProperty,objectProperty.getInverseProperty());
//			when not doing invRew we were doing just this:			
//			axiomsNormalizedO.add(axiom);
		}
		public void visit(OWLAsymmetricObjectPropertyAxiom axiom) {
			axiomsNormalizedO.add(axiom);
		}
		public void visit(OWLEquivalentObjectPropertiesAxiom axiom) {
			Set<OWLObjectPropertyExpression> objectPropertyExpressions=axiom.getProperties();
			if (objectPropertyExpressions.size()>1) {
				Iterator<OWLObjectPropertyExpression> iterator=objectPropertyExpressions.iterator();
				OWLObjectPropertyExpression first=iterator.next();
				OWLObjectPropertyExpression last=first;
				while (iterator.hasNext()) {
					OWLObjectPropertyExpression next=iterator.next();
					//						addInclusion(last,next);
					axiomsNormalizedO.add(m_factory.getOWLSubObjectPropertyOfAxiom(last, next));
					objectPropertyManager.registerPropertyInclusion(last, next);
					last=next;
				}
				//					addInclusion(last,first);
				axiomsNormalizedO.add(m_factory.getOWLSubObjectPropertyOfAxiom(last, first));
				objectPropertyManager.registerPropertyInclusion(last, first);
			}
			//				for (OWLObjectPropertyExpression objectPropertyExpression : objectPropertyExpressions)
			//					m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(objectPropertyExpression.getNamedProperty());
		}

		public void visit(OWLDisjointObjectPropertiesAxiom axiom) {// with only two properties each // are we taking this yet as in SHOIQ?
			Set<OWLObjectPropertyExpression> disjointProperties = axiom.getProperties(); 
			List<OWLObjectPropertyExpression> disjointPropertiesSimplified=new ArrayList<OWLObjectPropertyExpression>(disjointProperties.size());
			for (OWLObjectPropertyExpression p : disjointProperties)
				disjointPropertiesSimplified.add(p.getSimplified());
			for (int i = 0 ; i < disjointPropertiesSimplified.size() ; i++)
				for (int j = i+1 ; j < disjointPropertiesSimplified.size() ; j++){
					OWLDisjointObjectPropertiesAxiom ax = m_factory.getOWLDisjointObjectPropertiesAxiom(disjointPropertiesSimplified.get(i), disjointPropertiesSimplified.get(j));
					axiomsNormalizedO.add(ax);		
				}
		}
		//			public void visit(OWLDisjointObjectPropertiesAxiom axiom) {
		//				OWLObjectPropertyExpression[] objectPropertyExpressions=new OWLObjectPropertyExpression[axiom.getProperties().size()];
		//				axiom.getProperties().toArray(objectPropertyExpressions);
		//				for (int i=0;i<objectPropertyExpressions.length;i++) {
		//					objectPropertyExpressions[i]=objectPropertyExpressions[i].getSimplified();
		//					m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(objectPropertyExpressions[i].getNamedProperty());
		//				}
		//				m_axioms.m_disjointObjectProperties.add(objectPropertyExpressions);
		//			}
		public void visit(OWLInverseObjectPropertiesAxiom axiom) {
			OWLObjectPropertyExpression first=axiom.getFirstProperty().getSimplified();
			OWLObjectPropertyExpression second=axiom.getSecondProperty().getSimplified();
			axiomsNormalizedO.add(m_factory.getOWLSubObjectPropertyOfAxiom(first,second.getInverseProperty().getSimplified()));
			axiomsNormalizedO.add(m_factory.getOWLSubObjectPropertyOfAxiom(second,first.getInverseProperty().getSimplified()));

			objectPropertyManager.registerPropertyInclusion(first, second.getInverseProperty());
			objectPropertyManager.registerPropertyInclusion(second, first.getInverseProperty());

		}

		@Override
		public void visit(OWLObjectPropertyDomainAxiom axiom) {
			OWLClassExpression domain = axiom.getDomain();
			OWLObjectPropertyExpression p = axiom.getProperty();
			if (domain instanceof OWLClass)
				objectPropertyManager.registerDomain(p, (OWLClass) domain);
			else{
				domain = positive(domain);
				OWLClass def = (OWLClass) getDefinitionFor(domain, m_alreadyExists, true);
				m_classExpressionInclusionsAsDisjunctions.add(new OWLClassExpression[]{def.getComplementNNF(), domain});
				objectPropertyManager.registerDomain(p, def);
			}
		}
		public void visit(OWLObjectPropertyRangeAxiom axiom) {
			OWLClassExpression range = axiom.getRange();
			OWLObjectPropertyExpression p = axiom.getProperty();
			if (range instanceof OWLClass)
				objectPropertyManager.registerRange(p, (OWLClass) range);
			else{
				range = positive(range);
				OWLClass def = (OWLClass) getDefinitionFor(range, m_alreadyExists, true);
				m_classExpressionInclusionsAsDisjunctions.add(new OWLClassExpression[]{def.getComplementNNF(), range});
				objectPropertyManager.registerRange(p, def);
			}
		}
		public void visit(OWLFunctionalObjectPropertyAxiom axiom) {
			m_classExpressionInclusionsAsDisjunctions.add(new OWLClassExpression[] { m_factory.getOWLObjectMaxCardinality(1,axiom.getProperty().getSimplified()) });
			//				m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(axiom.getProperty().getNamedProperty());
		}
		public void visit(OWLInverseFunctionalObjectPropertyAxiom axiom) {
			m_classExpressionInclusionsAsDisjunctions.add(new OWLClassExpression[] { m_factory.getOWLObjectMaxCardinality(1,axiom.getProperty().getSimplified().getInverseProperty()) });
			//				m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(axiom.getProperty().getNamedProperty());
		}





		public void visit(OWLHasKeyAxiom axiom) {
			axiomsNormalizedO.add(axiom);
		}
		public void visit(SWRLRule rule) {
			axiomsNormalizedO.add(rule);
		}


		// Data property axioms
		public void visit(OWLSubDataPropertyOfAxiom axiom) {
			axiomsNormalizedO.add(axiom);
		}
		public void visit(OWLEquivalentDataPropertiesAxiom axiom) {
			axiomsNormalizedO.add(axiom);
		}
		public void visit(OWLDisjointDataPropertiesAxiom axiom) {
			axiomsNormalizedO.add(axiom);
		}
		public void visit(OWLDataPropertyDomainAxiom axiom) {
			axiomsNormalizedO.add(axiom);
		}
		public void visit(OWLDataPropertyRangeAxiom axiom) {
			axiomsNormalizedO.add(axiom);
		}
		public void visit(OWLFunctionalDataPropertyAxiom axiom) {
			axiomsNormalizedO.add(axiom);
		}

		protected void checkTopDataPropertyUse(OWLDataPropertyExpression dataPropertyExpression,OWLAxiom axiom) {
			//        if (dataPropertyExpression.isOWLTopDataProperty())
			//            throw new IllegalArgumentException("Error: In OWL 2 DL, owl:topDataProperty is only allowed to occur in the super property position of SubDataPropertyOf axioms, but the ontology contains an axiom "+axiom+" that violates this condition.");
		}

		// Assertions

		public void visit(OWLSameIndividualAxiom axiom) {
			if (axiom.containsAnonymousIndividuals())
				throw new IllegalArgumentException("The axiom "+axiom+" contains anonymous individuals, which is not allowed in OWL 2. ");
			axiomsNormalizedO.add(axiom);
		}
		public void visit(OWLDifferentIndividualsAxiom axiom) {
			if (axiom.containsAnonymousIndividuals())
				throw new IllegalArgumentException("The axiom "+axiom+" contains anonymous individuals, which is not allowed in OWL 2. ");
			axiomsNormalizedO.add(axiom);
		}
		public void visit(OWLClassAssertionAxiom axiom) {
			OWLClassExpression classExpression=axiom.getClassExpression();
			if (classExpression instanceof OWLDataHasValue) {
				//					OWLDataHasValue hasValue=(OWLDataHasValue)classExpression;
				//					addFact(m_factory.getOWLDataPropertyAssertionAxiom(hasValue.getProperty(), axiom.getIndividual(), hasValue.getValue()));
				//					return;
				Logger_MORe.logError("DATA PROPERTY!?");
			}
			if (classExpression instanceof OWLDataSomeValuesFrom) {
				//					OWLDataSomeValuesFrom someValuesFrom=(OWLDataSomeValuesFrom)classExpression;
				//					OWLDataRange dataRange=someValuesFrom.getFiller();
				//					if (dataRange instanceof OWLDataOneOf) {
				//						OWLDataOneOf oneOf=(OWLDataOneOf)dataRange;
				//						if (oneOf.getValues().size()==1) {
				//							addFact(m_factory.getOWLDataPropertyAssertionAxiom(someValuesFrom.getProperty(),axiom.getIndividual(),oneOf.getValues().iterator().next()));
				//							return;
				//						}
				//					}
				Logger_MORe.logError("DATA PROPERTY!?");
			}
			classExpression=positive(classExpression);
			if (!isSimple(classExpression)) {
				OWLClassExpression definition=getDefinitionFor(classExpression,m_alreadyExists);
				if (!m_alreadyExists[0])
					m_classExpressionInclusionsAsDisjunctions.add(new OWLClassExpression[] { negative(definition),classExpression });
				classExpression=definition;
			}
			axiomsNormalizedO.add(m_factory.getOWLClassAssertionAxiom(classExpression,axiom.getIndividual()));
		}
		public void visit(OWLObjectPropertyAssertionAxiom axiom) {
			axiomsNormalizedO.add(m_factory.getOWLObjectPropertyAssertionAxiom(axiom.getProperty().getSimplified(),axiom.getSubject(),axiom.getObject()));
			//				m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(axiom.getProperty().getNamedProperty());
		}
		public void visit(OWLNegativeObjectPropertyAssertionAxiom axiom) {
			if (axiom.containsAnonymousIndividuals())
				throw new IllegalArgumentException("The axiom "+axiom+" contains anonymous individuals, which is not allowed in OWL 2 DL. ");
			axiomsNormalizedO.add(m_factory.getOWLNegativeObjectPropertyAssertionAxiom(axiom.getProperty().getSimplified(),axiom.getSubject(),axiom.getObject()));
			//				m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(axiom.getProperty().getNamedProperty());
		}
		public void visit(OWLDataPropertyAssertionAxiom axiom) {
			Logger_MORe.logError("DATA PROPERTY!?");
			//				checkTopDataPropertyUse(axiom.getProperty(),axiom);
			//				addFact(axiom);
		}
		public void visit(OWLNegativeDataPropertyAssertionAxiom axiom) {
			Logger_MORe.logError("DATA PROPERTY!?");
			//				checkTopDataPropertyUse(axiom.getProperty(),axiom);
			//				if (axiom.containsAnonymousIndividuals())
			//					throw new IllegalArgumentException("The axiom "+axiom+" contains anonymous individuals, which is not allowed in OWL 2 DL. ");
			//				addFact(axiom);
		}

	}

	protected class ClassExpressionNormalizer4MORe extends ClassExpressionNormalizer{
		//        protected final Collection<OWLClassExpression[]> m_newInclusions;
		//        protected final Collection<OWLDataRange[]> m_newDataRangeInclusions;
		//        protected final boolean[] m_alreadyExists;

		public ClassExpressionNormalizer4MORe(Collection<OWLClassExpression[]> newInclusions) {
			super(newInclusions, new ArrayList<OWLDataRange[]>());
		}
		public OWLClassExpression visit(OWLObjectComplementOf object) {
			if (isNominal(object.getOperand())) {
				OWLObjectOneOf objectOneOf=(OWLObjectOneOf)object.getOperand();
				OWLClass definition=getDefinitionForNegativeNominal(objectOneOf,m_alreadyExists);
				if (!m_alreadyExists[0])
					for (OWLIndividual individual : objectOneOf.getIndividuals())
						axiomsNormalizedO.add(m_factory.getOWLClassAssertionAxiom(definition,individual));
				return m_factory.getOWLObjectComplementOf(definition);
			}
			else
				return object;
		}

		public OWLClassExpression visit(OWLObjectSomeValuesFrom object) {
			//				m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(object.getProperty().getNamedProperty());
			OWLClassExpression filler=object.getFiller();
			if (isSimple(filler)) //(filler instanceof OWLClass)
				return object;
			else {
				//            	OWLClassExpression definition=getDefinitionFor(filler,m_alreadyExists);
				OWLClassExpression definition=getDefinitionFor(filler,m_alreadyExists,true);//forcePositive=true
				if (!m_alreadyExists[0])
					m_newInclusions.add(new OWLClassExpression[] { negative(definition),filler });
				return m_factory.getOWLObjectSomeValuesFrom(object.getProperty(),definition);
			}
		}
		public OWLClassExpression visit(OWLObjectAllValuesFrom object) {
			//	            m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(object.getProperty().getNamedProperty());
			OWLClassExpression filler=object.getFiller();
			if (isSimple(filler))// || isNominal(filler) || isNegatedOneNominal(filler))
				//	                // The nominal cases are optimizations.
				return object;
			else {
				OWLClassExpression definition=getDefinitionFor(filler, m_alreadyExists, false);
				if (!m_alreadyExists[0])
					m_newInclusions.add(new OWLClassExpression[] { negative(definition),filler });
				return m_factory.getOWLObjectAllValuesFrom(object.getProperty(),definition);
			}
		}
		public OWLClassExpression visit(OWLObjectMinCardinality object) {
			//				m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(object.getProperty().getNamedProperty());
			OWLClassExpression filler=object.getFiller();
			//want to transform this into existential restrictions
			if (object.getCardinality() > 1){
				OWLClass[] disjointClasses = new OWLClass[object.getCardinality()];
				OWLClass freshClass = getFreshClass();
				for (int i = 0 ; i < disjointClasses.length ; i++){
					disjointClasses[i] = getFreshClass();
					m_newInclusions.add(
							new OWLClassExpression[]{
									freshClass.getComplementNNF(),
									m_factory.getOWLObjectSomeValuesFrom(object.getProperty().getSimplified(), disjointClasses[i])});
				}
				for (int i = 0 ; i < disjointClasses.length ; i++)
					for (int j = i+1 ; j < disjointClasses.length ; j++)
						m_newInclusions.add(
								new OWLClassExpression[]{
										disjointClasses[i].getComplementNNF(),
										disjointClasses[j].getComplementNNF()});

				for (int i = 0 ; i < disjointClasses.length ; i++)
					m_newInclusions.add(
							new OWLClassExpression[]{
									disjointClasses[i].getComplementNNF(),
									filler});

				return freshClass;
			} 
			else if (object.getCardinality() == 1){
				if (isSimple(filler))
					return m_factory.getOWLObjectSomeValuesFrom(object.getProperty().getSimplified(),filler);
				else {
					OWLClassExpression definition=getDefinitionFor(filler,m_alreadyExists, true);
					if (!m_alreadyExists[0])
						m_newInclusions.add(new OWLClassExpression[] { negative(definition),filler });
					return m_factory.getOWLObjectSomeValuesFrom(object.getProperty().getSimplified(),definition);
				}
			} 
			else
				return m_factory.getOWLThing();
		}
		public OWLClassExpression visit(OWLObjectMaxCardinality object) {
			//				m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(object.getProperty().getNamedProperty());
			OWLClassExpression filler=object.getFiller();
			if (object.getCardinality() == 0){
				filler = filler.getComplementNNF();
				OWLClassExpression c = m_factory.getOWLObjectAllValuesFrom(object.getProperty().getSimplified(), filler);
				return c.accept(this);
			}
			else
				if (isSimple(filler))
					return object;
				else {//not 100% about this case...
					OWLClassExpression complementDescription=m_expressionManager.getComplementNNF(filler);
					OWLClassExpression definition=getDefinitionFor(complementDescription,m_alreadyExists);
					if (!m_alreadyExists[0])
						m_newInclusions.add(new OWLClassExpression[] { negative(definition),complementDescription });
					return m_factory.getOWLObjectMaxCardinality(object.getCardinality(),object.getProperty(),m_expressionManager.getComplementNNF(definition));
				}
		}

	}

	protected class NormalizedAxiomRearranger implements OWLClassExpressionVisitor {
		protected Set<OWLClassExpression> m_lhsDisjuncts;
		protected Set<OWLClassExpression> m_rhsConjuncts;
		protected SortedGCI sortedGci;

		//need to save these

		public NormalizedAxiomRearranger() {
			m_lhsDisjuncts=new HashSet<OWLClassExpression>();
			m_rhsConjuncts=new HashSet<OWLClassExpression>();
			sortedGci = new SortedGCI();
		}

		protected void clear(){
			m_lhsDisjuncts.clear();
			m_rhsConjuncts.clear();
			sortedGci = new SortedGCI();
		}

		public OWLAxiom rearrange(OWLClassExpression[] inclusion){
			clear();

			for (OWLClassExpression description : inclusion)
				description.accept(this);

			//				OWLAxiom ax = m_factory.getOWLSubClassOfAxiom(getLhsAsIntersection(), getRhsAsUnion());
			return m_factory.getOWLSubClassOfAxiom(getLhsAsIntersection(), getRhsAsUnion());
		}

		public SortedGCI getSortedGCI(){
			return sortedGci;
		}

		protected OWLClassExpression getLhsAsIntersection(){
			if (m_lhsDisjuncts.isEmpty())
				return m_factory.getOWLThing();
			else if (m_lhsDisjuncts.size() == 1)
				return m_lhsDisjuncts.iterator().next();
			else 
				return m_factory.getOWLObjectIntersectionOf(m_lhsDisjuncts);
		}

		protected OWLClassExpression getRhsAsUnion(){
			if (m_rhsConjuncts.isEmpty())
				return m_factory.getOWLNothing();
			else if (m_rhsConjuncts.size() == 1)
				return m_rhsConjuncts.iterator().next();
			else 
				return m_factory.getOWLObjectUnionOf(m_rhsConjuncts);
		}


		// Various types of descriptions

		public void visit(OWLClass object) {
			m_rhsConjuncts.add(object);
			if (forInverseRewriting)
				sortedGci.addRhsAtomic(object);
		}
		public void visit(OWLObjectIntersectionOf object) {
			throw new IllegalStateException("Internal error: invalid normal form.");
		}
		public void visit(OWLObjectUnionOf object) {
			throw new IllegalStateException("Internal error: invalid normal form.");
		}
		public void visit(OWLObjectComplementOf object) {
			OWLClassExpression description=object.getOperand();
			if (forInverseRewriting){
				if (description instanceof OWLClass){
					m_lhsDisjuncts.add(description);
					if (forInverseRewriting)
						sortedGci.addLhsAtomic((OWLClass) description);
				}
				else 
					throw new IllegalStateException("Internal error: invalid normal form.");
			}
			else{ 
				if (!(description instanceof OWLClass || description instanceof OWLObjectHasSelf))
					throw new IllegalStateException("Internal error: invalid normal form.");
				else
					m_lhsDisjuncts.add(description);
			}
		}
		public void visit(OWLObjectOneOf object) {    
			m_rhsConjuncts.add(object);
			if (forInverseRewriting)
				sortedGci.addRhsOneOf(object);
		}
		public void visit(OWLObjectSomeValuesFrom object) {
			m_rhsConjuncts.add(object);
			if (forInverseRewriting)
				sortedGci.addRhsExist(object);
		}
		public void visit(OWLObjectAllValuesFrom object) {
			OWLClassExpression filler=object.getFiller();
			if (filler instanceof OWLClass && !(filler.isOWLNothing())){
				m_rhsConjuncts.add(object);
				if (forInverseRewriting)
					sortedGci.addRhsUniv(object);
			}
			else if ( filler.isOWLNothing()){
				OWLObjectSomeValuesFrom some = m_factory.getOWLObjectSomeValuesFrom(object.getProperty().getSimplified(), m_factory.getOWLThing()); 
				m_lhsDisjuncts.add(some);
				if (forInverseRewriting)
					sortedGci.addLhsExist(some);
			}
			else if (filler instanceof OWLObjectComplementOf){
				OWLObjectSomeValuesFrom some = m_factory.getOWLObjectSomeValuesFrom(object.getProperty().getSimplified(), object.getFiller().getComplementNNF()); 
				m_lhsDisjuncts.add(some);
				if (forInverseRewriting)
					sortedGci.addLhsExist(some);
			}
			else
				throw new IllegalStateException("Internal error: invalid normal form: " + object.toString());
		}
		public void visit(OWLObjectHasSelf object) {
			//what happens if this occurred on the lhs of some axiom??
			//how does it get treated in the first place when finding the NNF??
			m_rhsConjuncts.add(object);
			if (forInverseRewriting)
				sortedGci.addRhsExist(object);
		}
		public void visit(OWLObjectMinCardinality object) {
			//				//have I forgotten to treat this when its cardinality is 1 in all other methods in the class??
			//				m_rhsConjuncts.add(object);
			throw new IllegalStateException("min cardinality restrictions should have been rewritten away!");
		}
		public void visit(OWLObjectMaxCardinality object) {
			m_rhsConjuncts.add(object);
			if (forInverseRewriting)
				sortedGci.addRhsMaxCard(object);
		}
		public void visit(OWLObjectHasValue object) {
			m_rhsConjuncts.add(object);
			if (forInverseRewriting)
				sortedGci.addRhsExist(object);
		}
		public void visit(OWLObjectExactCardinality object) {
			m_rhsConjuncts.add(object);
		}
		public void visit(OWLDataSomeValuesFrom object) {
			m_rhsConjuncts.add(object);
		}
		public void visit(OWLDataAllValuesFrom object) {
			m_rhsConjuncts.add(object);
		}
		public void visit(OWLDataHasValue object) {
			m_rhsConjuncts.add(object);
		}
		public void visit(OWLDataMinCardinality object) {
			m_rhsConjuncts.add(object);
		}
		public void visit(OWLDataMaxCardinality object) {
			m_rhsConjuncts.add(object);
		}
		public void visit(OWLDataExactCardinality object) {
			m_rhsConjuncts.add(object);
		}
	}


}