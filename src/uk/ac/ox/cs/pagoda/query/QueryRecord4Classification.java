package uk.ac.ox.cs.pagoda.query;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.more.pagoda.IndividualManager;
import org.semanticweb.more.pagoda.QueryManager4Classification;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.more.util.Utility;

public class QueryRecord4Classification extends QueryRecord {

	
//	private String queryText; 
//	private int queryID = -1; 
//	private String[] answerVariables = null;
//	private Set<AnswerTuple> soundAnswerTuples = new HashSet<AnswerTuple>(); 
//	private Set<AnswerTuple> gapAnswerTuples = null;
	
//	protected QueryManager m_manager; 
	
	protected String queryEntity;
	protected ClassificationQueryType queryType;
	
	public QueryRecord4Classification(
			QueryManager4Classification queryManager,
			String queryText, int id, ClassificationQueryType type,
			String entity) {
		super(queryManager, queryText, id, 0);
		queryEntity = entity;
		queryType = type;
	}


	
	@Override
	public boolean updateUpperBoundAnswers(AnswerTuples answerTuples) {
		Set<AnswerTuple> tupleSet = new HashSet<AnswerTuple>();
		String str; 
		AnswerTuple tuple;
		for (; answerTuples.isValid(); answerTuples.moveNext()) {
			tuple = answerTuples.getTuple();
			str = tuple.toString(); 
			if (acceptAnswer(str) && !soundAnswerTuples.contains(tuple))
				tupleSet.add(tuple);
		}
	
		if (gapAnswerTuples == null) {
			gapAnswerTuples = tupleSet; 
			
			Logger_MORe.logDebug("The number of answers in the upper bound: " + (soundAnswerTuples.size() + gapAnswerTuples.size()));
			return true; 
		}
		
		boolean update = false; 
		for (Iterator<AnswerTuple> iter = gapAnswerTuples.iterator(); iter.hasNext(); ) {
			tuple = iter.next(); 
			if (!tupleSet.contains(tuple)) {
				iter.remove(); 
				update = true; 
			}
		}
		
		Logger_MORe.logDebug("The number of answers in the upper bound: " + (soundAnswerTuples.size() + gapAnswerTuples.size()));
		
		return update; 
	}
	
	
	protected boolean acceptAnswer(String answer){
		if (queryType == ClassificationQueryType.INDIVIDUAL)
			return !Utility.isInternalPredicate(answer);
		else
			return IndividualManager.isInstantiationIndividual(answer);
	}
	

//	protected boolean containsAuxPredicate(String str) {
//		return  Utility.isInternalPredicate(str); 
//	}
//	public AnswerTuples getAnswers() {
//		if (processed())
//			return getLowerBoundAnswers();
//		
//		return getUpperBoundAnswers(); 
//	}
	


	public Set<AnswerTuple> getGapAnswerTuples(){
		return gapAnswerTuples;
	}
	
	public Set<AnswerTuple> getLowerBoundAnswerTuples() {
		return soundAnswerTuples; 
	}
	
//	public Set<AnswerTuple> getUpperBoundAnswerTuples() {
//		Set<AnswerTuple> ret = new HashSet<AnswerTuple>(soundAnswerTuples);
//		ret.addAll(gapAnswerTuples);
//		return ret; 
//	}
	

	public DLClause getClause() {
		return null;
//		if (queryClause != null)
//			return queryClause; 
//		return queryClause = DLClauseHelper.getQuery(queryText, null); 
	}

//	public boolean isBottom() {  //we will never want to distinguish between bottom and other queries - right??
//		return queryID == 0;
//	}

	
	public void dispose() {
		super.dispose();
		//TODO may want to dispose some extra stuff - otherwise delete
	}
	
	
	public String getQueryEntity(){
		return queryEntity;
	}

	public ClassificationQueryType getQueryType(){
		return queryType;
	}
	
}
