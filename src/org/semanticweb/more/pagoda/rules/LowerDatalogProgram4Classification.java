package org.semanticweb.more.pagoda.rules;
import java.util.HashSet;
import java.util.Set;

import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLObjectHasSelf;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.profiles.OWL2ELProfile;
import org.semanticweb.owlapi.profiles.OWLProfileReport;
import org.semanticweb.owlapi.profiles.OWLProfileViolation;

import uk.ac.ox.cs.pagoda.approx.RLPlusOntology;
import uk.ac.ox.cs.pagoda.constraints.NullaryBottom;
import uk.ac.ox.cs.pagoda.constraints.PredicateDependency;
import uk.ac.ox.cs.pagoda.constraints.UnaryBottom;
import uk.ac.ox.cs.pagoda.owl.OWLHelper;
import uk.ac.ox.cs.pagoda.rules.LowerDatalogProgram;
import uk.ac.ox.cs.pagoda.util.Utility_PAGOdA;


public class LowerDatalogProgram4Classification extends LowerDatalogProgram {

	public LowerDatalogProgram4Classification(){
		super(false);
		m_approx = new IgnoreNonELandOverApproxExist4Classification();
	}


	public void loadRestrictedELontology(OWLOntology o) {
		OWLOntologyManager manager = o.getOWLOntologyManager();
		OWLDataFactory factory = manager.getOWLDataFactory();
		Set<OWLEntity> wholeSignature = new HashSet<OWLEntity>(o.getSignature());
		for (OWLEntity e : wholeSignature)
			manager.addAxiom(o, factory.getOWLDeclarationAxiom(e));

		OWLProfileReport report = new OWL2ELProfile().checkOntology(o);

		OWLOntology filteredOntology;
		try {
			filteredOntology = manager.createOntology(IRI.create(manager.getOntologyDocumentIRI(o).toString().replace(".owl", "-EL.owl")));
			manager.addAxioms(filteredOntology, o.getAxioms());
			for (OWLProfileViolation violation : report.getViolations()){
				//					Logger_MORe.logTrace(violation.toString());
				manager.removeAxiom(filteredOntology, violation.getAxiom());
			}
			Set<OWLAxiom> nominalOrReflexivityAxioms = new HashSet<OWLAxiom>();
			for (OWLAxiom ax : filteredOntology.getAxioms()){
				if (!ax.getIndividualsInSignature().isEmpty())
					nominalOrReflexivityAxioms.add(ax);
				else{
					for (OWLClassExpression exp : ax.getNestedClassExpressions()){
						if (exp instanceof OWLObjectHasSelf){
							nominalOrReflexivityAxioms.add(ax);
							break;
						}
					}
				}

			}
			for (OWLAxiom ax : nominalOrReflexivityAxioms)
				manager.removeAxiom(filteredOntology, ax);


			this.botStrategy = new UnaryBottom(); 
			RLPlusOntology owlOntology = new RLPlusOntology(); 
			owlOntology.load(filteredOntology, new NullaryBottom());
			owlOntology.simplify();

			ontology = owlOntology.getTBox(); 

			String ontologyPath = OWLHelper.getOntologyPath(ontology); 
			ontologyDirectory = ontologyPath.substring(0, ontologyPath.lastIndexOf(Utility_PAGOdA.FILE_SEPARATOR));
			clausify();
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}

	@Override
	public void transform() {
		super.transform();
		clauses.addAll(((IgnoreNonELandOverApproxExist4Classification) m_approx).getAuxiliaryClauses());
		//we don;t need to keep auxiliaryClauses separate from the other clauses here - as we do in the UpperProgram4Classification - because we are not going to do any tracking based on this program
	}

	@Override
	public String getOutputPath() {
		return getDirectory() + "lower.dlog";
	}

	public void setDependencyGraph(PredicateDependency graph){
		dependencyGraph = graph;
	}

}
