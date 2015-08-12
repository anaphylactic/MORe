package org.semanticweb.more.pagoda;

import org.semanticweb.more.util.Utility;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;
import uk.ac.ox.cs.pagoda.query.ClassificationQueryType;
import uk.ac.ox.cs.pagoda.query.QueryManager;
import uk.ac.ox.cs.pagoda.query.QueryRecord4Classification;

public class QueryManager4Classification extends QueryManager {
	
	
	
	String queryIndividual;
	String queryPredicate;
	
	
	
	public QueryRecord4Classification createBotQueryRecord4Classification() {
		
		return create(Utility.getQueryForClass(new OWLDataFactoryImpl().getOWLNothing()), ClassificationQueryType.PREDICATE, new OWLDataFactoryImpl().getOWLNothing().toString()); 
	}
	
	public QueryRecord4Classification create(String text, ClassificationQueryType queryType, String queryEntity) {
		QueryRecord4Classification ret = (QueryRecord4Classification) allRecords.get(text);  
		if (ret == null){
			ret = new QueryRecord4Classification(this, text, ++queryCounter, queryType, queryEntity); 
			allRecords.put(text, ret); 
			return ret; 
		}
		return ret;
	}
	
	
	
}


