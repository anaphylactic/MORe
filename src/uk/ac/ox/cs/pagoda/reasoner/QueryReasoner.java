package uk.ac.ox.cs.pagoda.reasoner;

import java.io.File;
import java.io.IOException;

import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.owlapi.model.OWLOntology;

import uk.ac.ox.cs.pagoda.query.AnswerTuples;
import uk.ac.ox.cs.pagoda.query.QueryManager;
import uk.ac.ox.cs.pagoda.query.QueryRecord;

public abstract class QueryReasoner {
	

	
	public static final String ImportDataFileSeparator = ";"; 
	protected StringBuilder importedData = new StringBuilder(); 
	
	public void importData(String datafile) {
		if (datafile != null)
			importData(datafile.split(ImportDataFileSeparator)); 
	}

	public void importData(String[] datafiles) {
		if (datafiles != null) {
			for (String datafile: datafiles) {
				File file = new File(datafile); 
				if (file.exists()) {
					if (file.isFile()) importDataFile(file);
					else importDataDirectory(file);
				}
				else {
					Logger_MORe.logDebug("warning: file " + datafile + " doesn't exists."); 
				}
			}
		}
	}
	
	private void importDataDirectory(File file) {
		for (File child: file.listFiles())
			if (child.isFile()) importDataFile(child);
			else importDataDirectory(child);
	}
	
	private void importDataFile(File file) {
		String datafile;
		try {
			datafile = file.getCanonicalPath();
		} catch (IOException e) {
			e.printStackTrace();
			return ; 
		} 
		importDataFile(datafile); 
	}
	
	protected final void importDataFile(String datafile) {
		if (importedData.length() == 0)
			importedData.append(datafile); 
		else 
			importedData.append(ImportDataFileSeparator).append(datafile);

	}
	
	public abstract void loadOntology(OWLOntology ontology);
	
	public abstract boolean preprocess(); 

//	public abstract boolean isConsistent(); 

//	public boolean fullReasoner = this instanceof MyQueryReasoner; 

	public abstract void evaluate(QueryRecord record);
	
	public abstract void evaluateUpper(QueryRecord record); 
	
	public AnswerTuples evaluate(String queryText, boolean forFacetGeneration) {
		if (forFacetGeneration) {
			QueryRecord record = m_queryManager.create(queryText);
			Logger_MORe.logInfo("---------- start evaluating upper bound for Query " + record.getQueryID() + " ----------", queryText);
			if (!record.processed())
				evaluateUpper(record);
			return record.getUpperBoundAnswers(); 
		}
		else 
			return evaluate(queryText); 
	}
	
	public AnswerTuples evaluate(String queryText) {
		QueryRecord record = m_queryManager.create(queryText); 
		Logger_MORe.logInfo("---------- start evaluating Query " + record.getQueryID() + " ----------", queryText);
		if (!record.processed())
			evaluate(record);
		return record.getAnswers(); 
	}
	
//	public void evaluate(Collection<QueryRecord> queryRecords) {
//		evaluate(queryRecords, null); 
//	}
//	
//	public void evaluate(Collection<QueryRecord> queryRecords, String answerFile) {
////		if (!isConsistent()) {	//commented by Ana - I don't need to check consistency for classification purposes
////			Utility.logDebug("The ontology and dataset is inconsistent."); 
////			return ; 
////		}
//		if (answerFile != null)
//			Utility_PAGOdA.redirectCurrentOut(answerFile);
//		Timer t = new Timer(); 
//		for (QueryRecord record: queryRecords) {
//			Logger_MORe.logInfo("---------- start evaluating Query " + record.getQueryID() + " ----------", 
//					record.getQueryText());
//			if (!record.processed()) {
//				t.reset();
//				if (!record.processed())
//					evaluate(record); 
//				if (!fullReasoner && !record.processed()) {
//					Logger_MORe.logDebug("The query has not been fully answered in " + t.duration() + " seconds."); 
//					continue; 
//				}
//				Logger_MORe.logInfo("Total time to answer this query: " + t.duration()); 
//			}
//			record.outputAnswers(false);
//			record.outputTimes();
//			record.dispose();
//		}
//
//		if (answerFile != null)
//			Utility_PAGOdA.closeCurrentOut();
//	}
	
	public abstract void dispose();  

	private QueryManager m_queryManager = new QueryManager(); 
	
	public QueryManager getQueryManager() {
		return m_queryManager; 
	}


//	public static QueryReasoner getHermiTReasoner(boolean toCheckSatisfiability) {
//		return new HermiTReasoner(toCheckSatisfiability);
//	}
	
}
