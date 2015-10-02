.. _sec-recipes:

What are Spekl Recipes?
======================

Spekl makes it easy to drop in new verification checks into your
projects. To that end we've created an easy to use reference of
available checks in Spekl we call "Recipes." Browse the sections below
to find out the kinds of checks you can add to your programs.


OpenJML
=======

.. image:: http://www.eecs.ucf.edu/~leavens/JML/images/jml-logo-med.png
	   :align: right


OpenJML is a suite of tools for editing, parsing, type-checking,
verifying (static checking), and run-time checking Java programs that
are annotated with JML statements stating what the program's methods
are supposed to do and the invariants the data structures should
obey. JML annotations state preconditions, postconditions, invariants
and the like about a method or class; OpenJML's tools will then check
that the implementation and the specifications are consistent.

The Java Modeling Language (JML) is a behavioral interface
specification language (BISL) that can be used to specify the behavior
of Java modules. It combines the design by contract approach of Eiffel
and the model-based specification approach of the Larch family of
interface specification languages, with some elements of the
refinement calculus.

More About this Tool:

-  `JML Specification Language <http://www.eecs.ucf.edu/~leavens/JML//index.shtml>`_
- `OpenJML Project Homepage <http://openjml.org>`_

Runtime Assertion Checking
--------------------------

Runtime Assertion Checking works by first compiling your program and
then running it with the assertions added to your program. The listing
below shows both checks configured. Note that the jml-java-7 specs
have been configured. In the example below, we output all of the
compiled classes to the ``out`` directory. This directory can be any
directory you like, just make sure it exists before running ``spm
check``.

.. code-block:: yaml

  checks :
    - name        : openjml-rac-compile
      description : "OpenJML All File RAC Compile"
      check       : rac-compile
      paths       : [MaybeAdd.java]
      classpath   : []
      out         : out       # the compile output directory

      tool:
        name      : openjml-rac
        
      specs:
        - name: jml-java-7
  
    - name        : openjml-rac-run
      description : "OpenJML All File RAC Check"
      check       : rac-check
      main        : MaybeAdd  # your main class
      paths       : [MaybeAdd.java]
      classpath   : []
      out         : out       # the compile output directory
      
      tool:
        name      : openjml-rac
  


Extended Static Checking
------------------------
Extended Static Checking is much more extensive in the types of errors
it can catch but is also generally harder to write specifications
for. Like the Runtime Assertion Checker, this check supports a
``classpath`` attribute that you can use to add classpath elements
needed to resolve all the classes in your project. 

.. code-block:: yaml
		
  checks :                                                                                                 
    - name        : openjml-esc                                                                            
      description : "OpenJML All File ESC"                                                                 
      paths       : [MaybeAdd.java]                                                                        
                                                                                                           
      tool:                                                                                                
        name      : openjml-esc                                                                            




FindBugs
========

.. image:: http://findbugs.sourceforge.net/umdFindbugs.png
	   :align: right
		   

FindBugs uses static analysis to inspect Java bytecode for occurrences
of bug patterns.  Static analysis means that FindBugs can find bugs by
simply inspecting a program's code: executing the program is not
necessary.  This makes FindBugs very easy to use: in general, you
should be able to use it to look for bugs in your code within a few
minutes of downloading it.  FindBugs works by analyzing Java bytecode
(compiled class files), so you don't even need the program's source
code to use it.  Because its analysis is sometimes imprecise, FindBugs
can report false warnings, which are warnings that do not indicate
real errors.  In practice, the rate of false warnings reported by
FindBugs is less than 50%.

More About this Tool:

- `FindBugs Project Homepage <http://findbugs.sourceforge.net/>`_



Run FindBugs and Generate HTML Reports
--------------------------------------


.. code-block:: yaml
		
  checks :
    - name        : findbugs-html
      description : "FindBugs HTML Report"
      check       : html
      paths       : [A.class]  # your class files
  
      tool:
        name      : findbugs



Run FindBugs and Generate XML Reports
--------------------------------------

.. code-block:: yaml
		
  checks :
    - name        : findbugs-xml
      description : "FindBugs XML Report"
      check       : xml
      paths       : [A.class]  # your classfiles
  
      tool:
        name      : findbugs

SAW
===

The Software Analysis Workbench (SAW) provides the ability to formally
verify properties of code written in C, Java, and Cryptol. It
leverages automated SAT and SMT solvers to make this process as
automated as possible, and provides a scripting language, called SAW
Script, to enable verification to scale up to more complex systems.

More About this Tool:

- `Galois Homepage <http://www.galois.com/>`_
- `SAW Project Homepage <http://saw.galois.com/>`_


Verify that Two Implementations are Equivalent
----------------------------------------------


.. code-block:: yaml
		
  checks :
    - name        : saw
      description : "SAW"
      check       : equiv-c
      paths       : [] #
      reference:
        file     : ffs_ref.c   # the reference file
        function : ffs_ref     # the reference function
      test:
        file     : ffs_test.c  # the file to check
        function : ffs_test    # the function to check
  
      tool:
        name      : saw


Checker Framework
=================

.. image:: http://types.cs.washington.edu/checker-framework/current/CFLogo.png
	   :align: right


Are you tired of null pointer exceptions, unintended side effects, SQL
injections, concurrency errors, mistaken equality tests, and other
run-time errors that appear during testing or in the field?

The Checker Framework enhances Java’s type system to make it more
powerful and useful. This lets software developers detect and prevent
errors in their Java programs. The Checker Framework includes compiler
plug-ins ("checkers") that find bugs or verify their absence. It also
permits you to write your own compiler plug-ins.

More About this Tool:

- `Checker Framework Homepage <http://types.cs.washington.edu/checker-framework/>`_


Nullness Checker
----------------

Note that this checker supports an optional ``classpath`` element,
which is a list of paths to add to the classpath. Also, if you do not
want your class files written to the same directory in which they
reside, you may use the ``out`` option to specify an output
directory. Note that it must exist before running ``spm check``.

See the `Nullness Checker Documentation <http://types.cs.washington.edu/checker-framework/current/checker-framework-manual.html#nullness-checker>`_

.. code-block:: yaml

  checks :                                                                                                 
    - name        : checker-framework-nullness
      check       : nullness
      description : "Checker Framework Nullness Check"                                                                 
      paths       : [MaybeAdd.java]                                                                        
                                                                                                           
      tool:                                                                                                
        name      : checker-framework                                                                            
  


Interning Checker
-----------------

Note that this checker supports an optional ``classpath`` element,
which is a list of paths to add to the classpath. Also, if you do not
want your class files written to the same directory in which they
reside, you may use the ``out`` option to specify an output
directory. Note that it must exist before running ``spm check``.

See the `Interning Checker Documentation <http://types.cs.washington.edu/checker-framework/current/checker-framework-manual.html#interning-checker>`_

.. code-block:: yaml

  checks :                                                                                                 
    - name        : checker-framework-interning
      check       : interning
      description : "Checker Framework Interning Check"                                                                 
      paths       : [MaybeAdd.java]                                                                        
                                                                                                           
      tool:                                                                                                
        name      : checker-framework                                                                            
  		


CheckLT : Taint Checking for Mere Mortals
=================

CheckLT is a program verification tool for Java which can help you use taint tracking to find defects in your software. CheckLT provides an easy to install verification toolset, a simple, non-invasive syntax for annotating programs, and a dynamically configurable security lattice.

More About this Tool:

- `CheckLT Homepage <http://checklt.github.io/>`_


Note that this checker supports an optional ``classpath`` element,
which is a list of paths to add to the classpath. Also, if you do not
want your class files written to the same directory in which they
reside, you may use the ``out`` option to specify an output
directory. Note that it must exist before running ``spm check``.

Note that for this to work, you must define a ``security.xml`` in the root directory of your project as described by the CheckLT documentation. 

.. code-block:: yaml

  checks :                                                                                                 
    - name        : checklt
      description : "CheckLT Lattice Tainting Check"                                                                 
      paths       : [MaybeAdd.java]                                                                        
                                                                                                           
      tool:                                                                                                
        name      : checklt                                                                            
  

