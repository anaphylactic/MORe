package org.semanticweb.more.util;


import java.io.PrintWriter;

import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.model.Individual;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLObjectInverseOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;

public class PrintingUtility {

	protected static final String RDF_TYPE = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type";

	public static void print(PrintWriter output, String objectIRI) {
		if (!objectIRI.startsWith("<"))
			objectIRI = "<" + objectIRI;
		if (!objectIRI.endsWith(">"))
			objectIRI = objectIRI + ">";
		output.print(objectIRI);
	}
	public static void print(PrintWriter output, OWLClass owlClass) {
		print(output, owlClass.getIRI().toString());
	}
	public static void print(PrintWriter output, Individual i) {
		print(output, i.getIRI().toString());
	}
	public static void print(PrintWriter output, OWLObjectPropertyExpression propertyExpression, Individual argument1, Individual argument2) throws Exception {
		if (propertyExpression instanceof OWLObjectProperty) {
			print(output, argument1);
			output.print(' ');
			print(output, ((OWLObjectProperty)propertyExpression).getIRI().toString());
			output.print(' ');
			print(output, argument2);
			output.println(" .");
		}
		else if (propertyExpression instanceof OWLObjectInverseOf)
			print(output, ((OWLObjectInverseOf)propertyExpression).getInverseProperty().getSimplified(), argument2, argument1);
		else
			throw new Exception("Unsupported property.");
	}
	public static void print(PrintWriter output, OWLClass owlClass, Individual argument) throws Exception {
		print(output, argument);
		output.print(' ');
		print(output, RDF_TYPE);
		output.print(' ');
		print(output, (owlClass).getIRI().toString());
		output.println(" .");
	}
	public static void print(PrintWriter output, OWLClass owlClass, String argument) throws Exception {
		print(output, argument);
		output.print(' ');
		print(output, RDF_TYPE);
		output.print(' ');
		print(output, (owlClass).getIRI().toString());
		output.println(" .");
	}
	public static void print(PrintWriter output, AtomicConcept concept, Individual argument) throws Exception {
		print(output, argument);
		output.print(' ');
		print(output, RDF_TYPE);
		output.print(' ');
		print(output, concept.getIRI().toString());
		output.println(" .");
	}
	
	public static void print(PrintWriter output, String propertyIRI, Individual argument1, Individual argument2) throws Exception {
		print(output, argument1);
		output.print(' ');
		print(output, propertyIRI);
		output.print(' ');
		print(output, argument2);
		output.println(" .");
	}
	public static void print(PrintWriter output, String classIRI, Individual argument) throws Exception {
		print(output, argument);
		output.print(' ');
		print(output, RDF_TYPE);
		output.print(' ');
		print(output, classIRI);
		output.println(" .");
	}
	public static void print(PrintWriter output, String propertyIRI, String argument1, String argument2) throws Exception {
		print(output, argument1);
		output.print(' ');
		print(output, propertyIRI);
		output.print(' ');
		print(output, argument2);
		output.println(" .");
	}
	public static void print(PrintWriter output, String classIRI, String argument) throws Exception {
		print(output, argument);
		output.print(' ');
		print(output, RDF_TYPE);
		output.print(' ');
		print(output, classIRI);
		output.println(" .");
	}


	/////////////////
	public static String print(String objectIRI) {
		if (!objectIRI.startsWith("<"))
			objectIRI = "<" + objectIRI;
		if (!objectIRI.endsWith(">"))
			objectIRI = objectIRI + ">";
		return objectIRI;
	}
	public static String print(OWLClass owlClass) {
		return print(owlClass.getIRI().toString());
	}
	public static String print(Individual i) {
		return print(i.getIRI().toString());
	}
	public static String print(OWLObjectPropertyExpression propertyExpression, Individual argument1, Individual argument2){
		if (propertyExpression instanceof OWLObjectProperty) {
			String ret = print(argument1);
			ret = ret + ' ';
			ret = ret + print(((OWLObjectProperty)propertyExpression).getIRI().toString());
			ret = ret + ' ';
			ret = ret + print(argument2);
			ret = ret + " .\n";
			return ret;
		}
		else if (propertyExpression instanceof OWLObjectInverseOf)
			return print(((OWLObjectInverseOf)propertyExpression).getInverseProperty().getSimplified(), argument2, argument1);
		else
			return "";
//			throw new Exception("Unsupported property.");
	}
	public static String print(OWLClass owlClass, Individual argument){
		String ret = print(argument);
		ret = ret + ' ';
		ret = ret + print(RDF_TYPE);
		ret = ret + ' ';
		ret = ret + print((owlClass).getIRI().toString());
		ret = ret + " .\n";
		return ret;
	}
	public static String print(String propertyIRI, Individual argument1, Individual argument2){
		String ret = print(argument1);
		ret = ret + ' ';
		ret = ret + print(propertyIRI);
		ret = ret + ' ';
		ret = ret + print(argument2);
		ret = ret + " .\n";
		return ret;
	}
	public static String print(String classIRI, Individual argument){
		String ret = print(argument);
		ret = ret + ' ';
		ret = ret + print(RDF_TYPE);
		ret = ret + ' ';
		ret = ret + print(classIRI);
		ret = ret + " .\n";
		return ret;
	}
	public static String print(String propertyIRI, String argument1, String argument2){
		String ret = print(argument1);
		ret = ret + ' ';
		ret = ret + print(propertyIRI);
		ret = ret + ' ';
		ret = ret + print(argument2);
		ret = ret + " .\n";
		return ret;
	}
	public static String print(String classIRI, String argument){
		String ret = print(argument);
		ret = ret + ' ';
		ret = ret + print(RDF_TYPE);
		ret = ret + ' ';
		ret = ret + print(classIRI);
		ret = ret + " .\n";
		return ret;
	}
}
