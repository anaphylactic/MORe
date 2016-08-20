package org.semanticweb.more.pagoda;

import uk.ac.ox.cs.pagoda.query.ClassificationQueryType;
import uk.ac.ox.cs.pagoda.query.QueryManager;
import uk.ac.ox.cs.pagoda.query.QueryRecord4Classification;
import uk.ac.ox.cs.pagoda.util.MyPrefixes;

public class QueryManager4Classification extends QueryManager {
	
	
	
	String queryIndividual;
	String queryPredicate;
	
	
	
	public QueryRecord4Classification createBotQueryRecord4Classification() {
		String bot = MyPrefixes.PAGOdAPrefixes.expandText("owl:Nothing");
		String query = "select ?x where { ?x " 
				+ MyPrefixes.PAGOdAPrefixes.expandText("rdf:type") + " " + bot + " }";
		return create(query, ClassificationQueryType.PREDICATE, bot); 
	}
	
	private QueryRecord4Classification create(String text, ClassificationQueryType queryType, String queryEntity) {
		QueryRecord4Classification ret = (QueryRecord4Classification) allRecords.get(text);  
		if (ret == null){
			ret = new QueryRecord4Classification(this, text, ++queryCounter, queryType, queryEntity); 
			allRecords.put(text, ret); 
			return ret; 
		}
		return ret;
	}
	
	public QueryRecord4Classification create(String text, String queryEntity) {//only individual queries can be created externally
		return create(text, ClassificationQueryType.INDIVIDUAL, queryEntity);
	}
	
	public static boolean isBottomQuery(QueryRecord4Classification queryRecord){
		return queryRecord.getQueryType() != ClassificationQueryType.INDIVIDUAL;
	}
	
}


