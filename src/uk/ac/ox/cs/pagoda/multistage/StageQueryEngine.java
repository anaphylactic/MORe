package uk.ac.ox.cs.pagoda.multistage;

import org.semanticweb.more.util.Logger_MORe;

import uk.ac.ox.cs.pagoda.query.AnswerTuples;
import uk.ac.ox.cs.pagoda.query.QueryRecord;
import uk.ac.ox.cs.pagoda.reasoner.light.BasicQueryEngine;

public abstract class StageQueryEngine extends BasicQueryEngine {
	
	protected boolean checkValidity; 
	
	public StageQueryEngine(String name, boolean checkValidity) {
		super(name);
		this.checkValidity = checkValidity; 
	}

//	public abstract void materialiseFoldedly(DatalogProgram dProgram, GapByStore4ID gap); 
//	
//	public abstract int materialiseRestrictedly(DatalogProgram dProgram, GapByStore4ID gap); 
	
	public void dispose() {
		super.dispose();
	}
	
	protected Boolean validMaterialisation = null; 

	public boolean isValid() {
		if (!checkValidity) return true; 
		if (validMaterialisation != null) return validMaterialisation; 
		
		validMaterialisation = false;
		
		AnswerTuples iter = null;
		try {
			iter = evaluate(QueryRecord.botQueryText);
			validMaterialisation = !iter.isValid();
			if (!validMaterialisation)
				outputAnswers(QueryRecord.botQueryText);
		} finally {
			if (iter != null) iter.dispose();
		}

		if (validMaterialisation)
			Logger_MORe.logInfo("The lazy-upper-bound store is valid."); 
		else 
			Logger_MORe.logInfo("The lazy-upper-bound store is not valid."); 
		return validMaterialisation;
	}

}
