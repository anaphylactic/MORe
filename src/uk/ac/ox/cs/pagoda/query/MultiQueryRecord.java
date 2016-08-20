package uk.ac.ox.cs.pagoda.query;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;

import uk.ac.ox.cs.pagoda.rules.GeneralProgram;


public class MultiQueryRecord {//extends QueryRecord {//it probably does not make sense for it to extend the class, too many things that don't really apply...
	

	Collection<QueryRecord4Classification> individualQueryRecords;
	
	OWLOntology relevantOntology = null; 
	Set<DLClause> relevantClauses = new HashSet<DLClause>(); 

	
	public MultiQueryRecord(Collection<QueryRecord4Classification> individualRecords) {
		individualQueryRecords = individualRecords;
	}

//	public MultiQueryRecord(Collection<QueryRecord4Classification> individualRecords) {
//		individualQueryRecords = individualRecords;
//	}
	
	
	public void removeQueries(Collection<QueryRecord4Classification> queryRecords){
		individualQueryRecords.removeAll(queryRecords);
		//we should probably reinitialise the other environment variables after doing this nut we won't bother with that for right now because we only call this method when then relevant ontology hasn't been computed yet
	}
	
	public Collection<QueryRecord4Classification> getIndividualQueryRecords(){
		return individualQueryRecords;
	}
	
	public void setRelevantOntology(OWLOntology knowledgebase) {
		relevantOntology = knowledgebase; 
		for (QueryRecord queryRecord : individualQueryRecords)
			queryRecord.setRelevantOntology(knowledgebase);
	}
	
	public OWLOntology getRelevantOntology() {
		return relevantOntology; 
	}

	public void saveRelevantOntology(String filename) {
		if (relevantOntology == null) return ; 
		OWLOntologyManager manager = relevantOntology.getOWLOntologyManager(); 
		try {
			FileOutputStream outputStream = new FileOutputStream(filename); 
			manager.saveOntology(relevantOntology, outputStream);
			outputStream.close();
		} catch (OWLOntologyStorageException e) {
			e.printStackTrace();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public void saveRelevantClause() {
		if (relevantClauses == null) return ; 
		GeneralProgram p = new GeneralProgram(relevantClauses, relevantOntology);
		p.save();
	}

	public void addRelevantClauses(DLClause clause){
		relevantClauses.add(clause);
	}
	
	public void clearClauses() {
		relevantClauses.clear();
	}
	
	public void dispose() {
		for (QueryRecord record : individualQueryRecords)
			record.dispose();
		if (individualQueryRecords != null) individualQueryRecords.clear();
		if (relevantClauses != null) relevantClauses.clear();
		if (relevantOntology != null)
			relevantOntology.getOWLOntologyManager().removeOntology(relevantOntology);
	}

	boolean processed = false; 

	public void markAsProcessed() {
		processed = true; 
	}
	
	
}
