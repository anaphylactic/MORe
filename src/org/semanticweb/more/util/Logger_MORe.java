package org.semanticweb.more.util;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;

import uk.ac.ox.cs.pagoda.util.Utility_PAGOdA;

public class Logger_MORe {
	
	private static final Logger logger = Logger.getLogger("org.semanticweb.more");
	
	private static String getLogMessage(Object[] messages) {
		StringBuilder logMessage = new StringBuilder();
		if (messages.length == 1) return messages[0].toString(); 
		else {
			logMessage.setLength(0);
			for (int i = 0; i < messages.length; ++i) { 
				if (logMessage.length() != 0)
					logMessage.append(Utility_PAGOdA.LINE_SEPARATOR); 
				logMessage.append(messages[i]); 
			}
			return logMessage.toString(); 		
		}

	}
	
	public static void logInfo(Object... messages){
		logger.info(getLogMessage(messages));
	}

	
	public static void logDebug(Object... messages){
		logger.debug(getLogMessage(messages));
	}

	
	public static void logError(Object... messages){
		logger.error(getLogMessage(messages));
	}

	
	public static void logTrace(Object... messages){
		logger.trace(getLogMessage(messages));
	}
	
	
	public static Level getLevel(){
		return logger.getLevel();
	}


	public static void setLevel(Level level){
		logger.setLevel(level);
		logInfo("Level set to " + level.toString());
	}

}
