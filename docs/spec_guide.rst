.. role:: raw-math(raw)
    :format: latex html

.. _sec-spec_guide:

Specification Authoring Guide
=============================

Specification authoring is central to the design of Spekl. In this
section you will learn how to author and publish specifications with
the help of Spekl. 


Authoring Standalone Specifications
===================================
The first, and easiest to understand mode of authoring is the case of
authoring standalone specifications. You can think of standalone
specifications as a specification project, in which you provide only
the contents of your specifications. Let's dive right in.

Creating the Project
--------------------
For this section, let's pretend that we are authoring specifications
for a fictional project called ``MaybeAdd``. To start, let's create a
project::

  ~ » mkdir maybe-add-specs
  ~ » spm init spec 

The ``spm`` tool will ask you a series of questions to set up this
project. There are a few important details to understand here:

.. _ref-authoring-requirements:

- You should specify a unique name for the project. I'm going to call
  mine ``maybe-add-specs`` -- but you'll have to pick something else
  since this command will register your project with the Spekl central
  repository.
- You'll need a valid GitHub account. When the wizard prompts you for
  a username, make sure you give your GitHub username. Also, the email
  and full name you specify here needs to be the email and full name
  you use on GitHub.
- After you create your project, you will get a email from GitHub
  asking you to join a team. **Accept this invite**. You'll need to do
  this before you can publish your specification. 

After this command completes, you'll have a single file in your
current directory called ``package.yml``. Let's have a look at that
file, now.

.. code-block:: yaml

  name        : maybe-add-specs          # name of the package
  version     : 0.0.1       # version of the package
  kind        : spec                     # one of tool or spec(s)
  description : a short description

  author:
    - name: John L. Singleton
      email: jsinglet@gmail.com


Note that the ``package.yml`` file supports all the usual
configuration elements supported in tool authoring. You can enforce
environmental conditions with the ``assumes`` configuration element,
you can create dependencies with the ``depends`` element and you can
add assets and installation commands with the ``assets`` and
``install`` configuration elements.

In general a specification library won't do these things but if you
need to, you can see the section in the tool authoring guide on
configuring these elements. See the :ref:`sec-tool_guide` for more
details.

Next you will want to start adding specifications to your library. As
an example, we'll add a specification in the ``JML`` language called
``MaybeAdd``. To do this, create a file in the current directory
called ``MaybeAdd.jml``.

.. code-block:: java

  public class MaybeAdd {
  
      //@ requires 0 < a && a < 1000;
      //@ requires 0 < b && b < 1000;
      //@ ensures  \result > 0;
      public static int add(int a, int b);
  
  }
  		

Ok, you've just authored your first specification with Spekl! Let's
publish your spec. To do that, execute the ``spm publish`` command::


  ~ » spm publish

As long as you met the requirements we mentioned earlier in this
section, you should now have a freshly published project. You can
continue working on this project by editing and doing a ``spm
publish`` at any time. Every time you publish, however, make sure to
increment the version number in your ``package.yml`` file. If you
don't Spekl will not allow you to publish.

  
Authoring Inline Specifications
===============================

In the last section we learned how to create stand alone
specifications. While this is the authoring mode most useful for
projects wishing to import existing specifications into Spekl, the
more general case for using Spekl is when one wants to author
specifications for a codebase that is under development. In this
section we are going to learn how to do that. We'll continue with the
example we've used in other sections, the ``MaybeAdd`` example.

To start, let's create a normal verification project::

   ~ » mkdir new-project
   ~ » cd new-project
   ~ » spm init 

Next, create the file ``MaybeAdd.java`` with the following content:

.. code-block:: java

  public class MaybeAdd {

    public static int add(int a, int b){
	return a-b;
    }

    
    public static void main(String args[]){

	System.out.println(MaybeAdd.add(1,2));

    }

  }


Note that this file does not contain specifications. Next, edit your
``spekl.yml`` file to be set up to do Runtime Assertion Checking with
OpenJML:

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


Next, we want to install all of the tools for this project::

   ~ » spm install

At this point, if we run ``spm check``, we will get no errors for our
code. That is because there are no specifications attached. Suppose
that we'd like to create a new specification library for our project
that we are working on. To do that, we execute the ``spm init spec``
command. Since we are in a directory with a ``spekl.yml`` file, Spekl
will detect that we want to do an *inline specification*. This will
create the specification in the ``.spm`` directory. Here's what the
command sequence looks like::

  $ spm init spec
  [spm] INFO  - [command-init]
  [spm] INFO  - [new-spec] Creating new spec project...
  Spec Name? [default: my spec] my-spec-1
  Spec Description? [default: a short description]
  Version? [default: 0.0.1]
  Author Name? [default: Some User] John L. Singleton
  Author Email? [default: user@email.com] jsinglet@gmail.com
  Username? (not stored) [default: someuser] xxxxxxxxxx
  name        : my-spec-1          # name of the package
  version     : 0.0.1       # version of the package
  kind        : spec                     # one of tool or spec(s)
  description : a short description
  
  author:
    - name: John L. Singleton
      email: jsinglet@gmail.com
  
  
  Does this configuration look reasonable? [Y/n] y
  [spm] INFO  - [new-spec] Writing configuration file to: .spm\my-spec-1-0.0.1\package.yml
  [spm] INFO  - [backend-init-at] Creating SPM repository connection...
  [spm] INFO  - [new-spec] Done.
  
	
Note that Spekl created the spec in the ``.spm/my-spec-1-0.0.1``
directory. This functions exactly like the standalone specifications
in the previous section but it can be authored alongside the project
you are currently working on.


Let's add some specifications to the library. To do that, create the
file ``MaybeAdd.jml`` with the following content in the newly created
directory under the ``.spm`` directory:

.. code-block:: java

  public class MaybeAdd {
  
      //@ requires 0 < a && a < 1000;
      //@ requires 0 < b && b < 1000;
      //@ ensures  \result > 0;
      public static int add(int a, int b);
  
  }


Next, update your ``spekl.yml`` file to contain a reference to your
new specification library. 

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
	- name: my-spec-1 #  <-- added my-spec here
  
    - name        : openjml-rac-run
      description : "OpenJML All File RAC Check"
      check       : rac-check
      main        : MaybeAdd  # your main class
      paths       : [MaybeAdd.java]
      classpath   : []
      out         : out       # the compile output directory
      
      tool:
        name      : openjml-rac

Now, let's try to run a check::

  $ spm check


  [spm] INFO  - [command-check] Running all checks for project...
  [spm] INFO  - [command-check] Running check: OpenJML All File RAC Compile
  [spm] INFO  - Running OpenJML RAC Compile...
  .spm\my-spec-1-0.0.1\MaybeAdd.jml:5: error: The token \result is illegal or not implemented for a type or method clause (JmlParser.classOrInterfaceBodyDeclaration)
      //@ \result == a+b;
          ^
  Note: .spm\jml-java-7-1.7-2\java\util\Arrays.jml uses unchecked or unsafe operations.
  Note: Recompile with -Xlint:unchecked for details.
  1 error
 
  [spm] INFO  - [command-check] Running check: OpenJML All File RAC Check
  [spm] INFO  - Running OpenJML RAC Program...
  

Now, as you can see, Spekl correctly picks up your specification
library. You can create as many specification libraries as you want
and add them to your project so as to specify different portions of
your codebase. This enables you to use different tools, different
checks, and different languages all within the same project.

As with stand alone projects, you can publish your changes by going
into your newly created specification directory under ``.spm`` and
typing ``spm publish``.

  
Where Do Published Specs Go?
=================================
After you've published your specs, you may want access them
directly. You can find your spec on GitHub at
http://github.com/Spekl/<your spec>


Advanced Topics in Specification Authoring
==========================================
For the more advanced reader, the following sections contain some
topics that pertain to some of Spekl's more advanced features for
specification authoring. 

Layering Specifications
-----------------------
Many times in specification writing you'll want to modify the
specification of some existing specification -- but use the other
parts of the specification. Spekl allows you do do this via
*Specification Extension*. In extension, you base your specifications
off of a pre-existing specification. Any modifications made to the
upstream specification are then automatically propagated down to your
specification.

For example, let's think about specifying the Java API. Java 7
contains many of the same functions and classes as Java 4, but with
some additions and changes. In turn, Java 6 could be based on Java 5
and so on. In Spekl, this is a perfect example of a
specification hierarchy. More formally, you can think of a
specification hierarchy as a chain of the form:

.. math::

   \overrightarrow{SH} = \{ (S_{\bot}, \mathscr{H_{\bot}}), \ldots, (S_{\top}, \mathscr{H_{\top}})\}
	  
Where :math:`\top` is the top of the hierarchy and :math:`\bot` is the
bottom. It is ordered by the relation given here:

.. math::

   (S', \mathscr{H}') \sqsupseteq (S, \mathscr{H}) \iff S' <: S \land \exists \delta \in \mathscr{H}' ~:~ \delta \in \mathscr{H}


To specify that a specification should extend another specification,
you use the ``spm extend`` command. During the process of creation you
give the name of a specification that exists.

When the creation process is over, you will now have a freshly created
specification project that is based on the upstream specification. Any
changes you make to your specification will be local to only your
specification, but now you will have the ability to ``refresh`` your
specification with respect to the upstream specification. 
 

Refreshing Layered Specifications
---------------------------------
Once you have created a downstream specification with the ``spm
extend`` command, you can either explicitly update your specification
with the changes in the upstream specification or allow it to happen
automatically at check time.

To update your specification with the most recent work on the upstream
specification, use the following command::

   ~ » spm refresh

This command will walk up the entire specification hierarchy and
refresh your specification if there has been any upstream work. Note
that if you do a ``spm publish``, these changes will become part of
the permanent history of your specification library (and will no
longer need to be refreshed). 
