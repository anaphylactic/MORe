package uk.ac.ox.cs.pagoda.approx;

import java.util.HashSet;
import java.util.Set;

import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLOntology;

public class Clausifier {

	OWLDataFactory factory; 
	Set<String> dataProperties = new HashSet<String>();

	public Clausifier(OWLOntology ontology) {
		factory = ontology.getOWLOntologyManager().getOWLDataFactory(); 
		for (OWLDataProperty dataProperty: ontology.getDataPropertiesInSignature(true))
			dataProperties.add(dataProperty.toStringID()); 
	}
	
	public Clause clasuify(DLClause clause) {
		return new Clause(this, clause); 
	}
	
}
