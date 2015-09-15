# MORe
Modular OWL 2 Reasoner for Ontology Classification

To build the project open a terminal, go to the project's directory and run
```
$ mkdir repo
$ mvn deploy:deploy-file -Durl=file:repo/ -Dfile=lib/RDFox/<platform>/JRDFox.jar -DgroupId=uk.ac.ox.cs -DartifactId=JRDFox -Dpackaging=jar -Dversion=build2213
```
where ```<platform>``` should be Mac, Linux or Windows.
If you wish to use PrisM as a library, run
```
$ mvn install
```
This should generate a folder called ```target``` containing the library ```uber-PrisM-0.0.1-SNAPSHOT.jar```. This library is ready to use and bundles all necessary dependencies.

Given an instance ```o``` of the ```OWLOntology``` class from  the [OWLAPI](http://owlapi.sourceforge.net/),  the simplest way to create an instance of the reasoner is the following:
```java
	MOReReasonerFactory factory = new MOReReasonerFactory();
	MoreReasoner more = factory.createReasoner(o);
```
To classify your ontology, simply call
```java
	more.classifyClasses();
```
You can retrieve all the superclasses of any ```OWLClass c``` in the input ontology by calling
```java
	more.getAllSuperClasses(c);
```
and also all unsatisfiable classes in the ontology with
```java
	more.getAllUnsatisfiableClasses();
```
The default configuration of MORe splits the classification workload between the reasoners ELK and HermiT, but you can configure MORe to split the workload between ELK, RDFox and HermiT
as follows
```java
	boolean useRDFox = true;
	MOReReasonerConfiguration config = new MOReReasonerConfiguration(useRDFox);
	MOReReasonerFactory factory = new MOReReasonerFactory();
	MOReReasoner more = factory.createReasoner(o, config);
```
It is also possible to make MORe combine ELK (and maybe RDFox) with any other OWL 2 reasoner that implements the ```OWLReasoner``` interface from the OWLAPI and can be created with an ```OWLReasonerFactory```. For this, it suffices to provide an instance ```owl2RsnrFactory``` of the corresponding ```OWLReasonerFactory``` and an instance  ```owl2RsnrConfig``` of the corresponding ```OWL2ReasonerConfiguration```  as arguments when creating ```more``` as follows:
```java
	MOReReasoner more = factory.createReasoner(o, config, owl2RsnrFactory, owl2RsnrConfig);
```