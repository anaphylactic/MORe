package org.semanticweb.more.util;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.HashSet;

import org.semanticweb.HermiT.model.Individual;
import org.semanticweb.owlapi.io.OWLFunctionalSyntaxOntologyFormat;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;

import uk.ac.ox.cs.JRDFox.JRDFStoreException;
import uk.ac.ox.cs.JRDFox.Prefixes;
import uk.ac.ox.cs.JRDFox.store.DataStore;
import uk.ac.ox.cs.JRDFox.store.Parameters;
import uk.ac.ox.cs.JRDFox.store.TupleIterator;
import uk.ac.ox.cs.pagoda.reasoner.light.RDFoxTripleManager;
import uk.ac.ox.cs.pagoda.tracking.TrackingRuleEncoder;
import uk.ac.ox.cs.pagoda.util.MyPrefixes;
import uk.ac.ox.cs.pagoda.util.Namespace;

public class Utility {



	public static String getOntologyID_ontologyForOWL2Reasoner(){
		return "http://www.cs.ox.ac.uk/isg/tools/MORe/ontologies/ontologyForOWL2Reasoner.owl";
	}

	public static String getOntologyID_workingOntology(){
		return "http://www.cs.ox.ac.uk/isg/tools/MORe/ontologies/working_copy.owl";
	}

	public static String getOntologyID_compModule(){
		return "http://www.cs.ox.ac.uk/isg/tools/MORe/ontologies/compmodule_copy.owl";
	}

	public static String getOntologyID_Lmodule(){
		return "http://www.cs.ox.ac.uk/isg/tools/MORe/ontologies/lmodule_copy.owl";
	}

	public static String getOntologyID_DLontology(){
		return "http://www.cs.ox.ac.uk/isg/tools/MORe/ontologies/dlOntology_copy.owl";
	}



	public static void saveOntology(OWLOntologyManager manager, OWLOntology o, String iri){
		manager.setOntologyDocumentIRI(o,IRI.create(iri));
		try {
			manager.saveOntology(o, new OWLFunctionalSyntaxOntologyFormat());
		} catch (OWLOntologyStorageException e) {
			e.printStackTrace();
		}
	}


	public static void printAllTriples(DataStore store){
		TupleIterator iter = null;
		try{
			String query = "select ?x ?y ?z where { ?x ?y ?z }";
			Parameters par = new Parameters();
			par.m_expandEquality = false;
			iter = store.compileQuery(query, new Prefixes(), par);
			for (long multi = iter.open() ; multi != 0 ; multi = iter.getNext()){
				String t1 = iter.getGroundTerm(0).toString();
				String t2 = iter.getGroundTerm(1).toString();
				String t3 = iter.getGroundTerm(2).toString();
				if (!(t2.equals(MyPrefixes.PAGOdAPrefixes.expandText("owl:sameAs")) && t1.equals(t3)))
					Logger_MORe.logTrace(t1 + " " + t2 + " " + t3);
			}
		}
		catch (JRDFStoreException e){
			e.printStackTrace();
		}
		finally{
			if (iter != null) iter.dispose();
		}
	}
	
	public static void printTriplesInvolvingIndividual(DataStore store, Individual ind){
		TupleIterator iter = null;
		try{
			String query = "select ?y ?z where { " + ind.toString() + " ?y ?z }";
			Parameters par = new Parameters();
			par.m_expandEquality = false;
			iter = store.compileQuery(query, new Prefixes(), par);
			for (long multi = iter.open() ; multi != 0 ; multi = iter.getNext()){
				String t1 = ind.toString();
				String t2 = iter.getGroundTerm(0).toString();
				String t3 = iter.getGroundTerm(1).toString();
				if (!(t2.equals(MyPrefixes.PAGOdAPrefixes.expandText("owl:sameAs")) && t1.equals(t3)))
					Logger_MORe.logInfo(t1 + " " + t2 + " " + t3);
			}
		}
		catch (JRDFStoreException e){
			e.printStackTrace();
		}
		finally{
			if (iter != null) iter.dispose();
		}
		try{
			String query = "select ?x ?y where { ?x ?y " + ind.toString() + " }";
			Parameters par = new Parameters();
			par.m_expandEquality = false;
			iter = store.compileQuery(query, new Prefixes(), par);
			for (long multi = iter.open() ; multi != 0 ; multi = iter.getNext()){
				String t1 = iter.getGroundTerm(0).toString();
				String t2 = iter.getGroundTerm(1).toString();
				String t3 = ind.toString();
				if (!(t2.equals(MyPrefixes.PAGOdAPrefixes.expandText("owl:sameAs")) && t1.equals(t3)))
					Logger_MORe.logInfo(t1 + " " + t2 + " " + t3);
			}
		}
		catch (JRDFStoreException e){
			e.printStackTrace();
		}
		finally{
			if (iter != null) iter.dispose();
		}
	}
	

	public static void exportStore(DataStore store, String toFile, boolean expandEquality){
		TupleIterator iter = null;
		try {
			PrintWriter out = new PrintWriter(new File(toFile));
			String query = "select ?x ?y ?z where { ?x ?y ?z }";
			Parameters par = new Parameters();
			par.m_expandEquality = expandEquality;
			iter = store.compileQuery(query, new Prefixes(), par);
			for (long multi = iter.open() ; multi != 0 ; multi = iter.getNext()){
				String t1 = iter.getGroundTerm(0).toString();
				String t2 = iter.getGroundTerm(1).toString();
				String t3 = iter.getGroundTerm(2).toString();

				PrintingUtility.print(out, t2,t1,t3);
			}
			out.close();
		}
		catch (JRDFStoreException e){
			e.printStackTrace();
		}
		catch (FileNotFoundException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		finally{
			if (iter != null) iter.dispose();
		}
	}

	public static void printStoreToFile(DataStore store, String filename) {
		TupleIterator tupleIterator = null;
		StringBuilder sb = new StringBuilder();
		try {
			tupleIterator = store.compileQuery("select ?x ?y ?z where { ?x ?y ?z }");
			int arity = tupleIterator.getArity();
			for (long multiplicity = tupleIterator.open(); multiplicity != 0; multiplicity = tupleIterator.getNext()) {
				for (int termIndex = 0; termIndex < arity; ++termIndex) {
					if (termIndex != 0)
						sb.append("  ");
					sb.append(RDFoxTripleManager.getRawTerm(tupleIterator.getResource(termIndex)));
				}
				sb.append("\n");
			}
			File f = new File(filename+".ttl");
			PrintWriter pw;
			try {
				pw = new PrintWriter(f);
				pw.print(sb.toString());
				pw.close();

				System.out.println("file saved to " + f.getAbsolutePath());

			} catch (FileNotFoundException e) {
				e.printStackTrace();
			}
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		} finally{
			if (tupleIterator != null) tupleIterator.dispose();
		}
	}


	public static void printPredicatesSummaryOfStoreToFile(DataStore store, String filename) {
		TupleIterator tupleIterator = null;
		StringBuilder sb = new StringBuilder();
		try {

			sb.append("BINARY\n\n");

			tupleIterator = store.compileQuery("select distinct ?y where { ?x ?y ?z }");
			int arity = tupleIterator.getArity();
			for (long multiplicity = tupleIterator.open(); multiplicity != 0; multiplicity = tupleIterator.getNext()) {
				for (int termIndex = 0; termIndex < arity; ++termIndex) {
					if (termIndex != 0)
						sb.append("  ");
					sb.append(RDFoxTripleManager.getRawTerm(tupleIterator.getResource(termIndex)));
				}
				sb.append(" * " + multiplicity);
				sb.append("\n");
			}
			tupleIterator.dispose();

			sb.append("\n\nUNARY\n\n");

			tupleIterator = store.compileQuery("select distinct ?z where { ?x " + MyPrefixes.PAGOdAPrefixes.expandText("rdf:type") + " ?z }");
			arity = tupleIterator.getArity();
			for (long multiplicity = tupleIterator.open(); multiplicity != 0; multiplicity = tupleIterator.getNext()) {
				for (int termIndex = 0; termIndex < arity; ++termIndex) {
					if (termIndex != 0)
						sb.append("  ");
					sb.append(RDFoxTripleManager.getRawTerm(tupleIterator.getResource(termIndex)));
				}
				sb.append(" * " + multiplicity);
				sb.append("\n");
			}



			File f = new File(filename+".ttl");
			PrintWriter pw;
			try {
				pw = new PrintWriter(f);
				pw.print(sb.toString());
				pw.close();

				System.out.println("file saved to " + f.getAbsolutePath());

			} catch (FileNotFoundException e) {
				e.printStackTrace();
			}
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		} finally{
			if (tupleIterator != null) tupleIterator.dispose();
		}
	}


	public static boolean isRDFoxInternalPredicate(String p){
		return p.contains("http://www.cs.ox.ac.uk/RDFox#replace");
	}
	public static boolean isHermiTInternalPredicate(String p){
		return p.contains("internal:def#") || p.contains("internal:nom#");
	}
	public static boolean isPAGOdAInternalPredicate(String p){
		return p.contains(Namespace.PAGODA_AUX) || p.contains("_AUX") || 
				p.contains(TrackingRuleEncoder.QueryPredicate);
		// || p.endsWith("_neg") || p.endsWith("_neg>");   		//we're not using the _neg concepts but if we were we would have to filter them out here too.
	}
	public static boolean isMOReInternalPredicate(String p){
		return p.contains("_directed>");
	}

	public static boolean isInternalPredicate(String p){
		return isHermiTInternalPredicate(p) || isRDFoxInternalPredicate(p) || isPAGOdAInternalPredicate(p) || isMOReInternalPredicate(p);
	}

	public static boolean isSkolemIndividual(String i){
		return i.contains(Namespace.PAGODA_ANONY);
	}

	public static String removeAngleBrackets(String s){
		return s.replace("<", "").replace(">", "");
	}

	public static boolean compareCollections(Collection<?> set1, Collection<?> set2){
		if (set1.size() != set2.size())
			return false;
		Collection<?> aux1 = new HashSet<Object>(set1);
		aux1.removeAll(set2);
		return aux1.isEmpty();
		//		Collection<?> aux2 = new HashSet<Object>(set2);
		//		aux2.removeAll(set1);
		//		return aux1.isEmpty() && aux2.isEmpty();
	}

	public static String getQueryForClass(OWLClass c){
		return "SELECT ?X\nWHERE {\n?X <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> " + c.toString() + "\n}"; 
	}
	public static String getQueryForIndividual(String ind){
		return "SELECT ?X\nWHERE {\n" + ind + " <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> ?X\n}"; 
	}
}
