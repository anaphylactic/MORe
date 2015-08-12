package uk.ac.ox.cs.pagoda.tracking;
import org.semanticweb.HermiT.model.DLClause;

import uk.ac.ox.cs.pagoda.query.MultiQueryRecord;


public interface TrackingRuleEncoder4Classification{

//	abstract void encodingClassificationQuery(QueryRecord record);//to add the tracking rules relating to this query
	abstract void encodeClassificationQueries(MultiQueryRecord record);

	abstract void encodingAuxiliaryRule(DLClause clause);
	
	abstract String getTrackingProgramOutputPath();
}
