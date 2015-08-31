Getting Started with Spekl
========================================

.. _DRY: http://en.wikipedia.org/wiki/Don't_repeat_yourself
.. _scaffolding: http://en.wikipedia.org/wiki/Scaffold_(programming)
.. _convention_over_configuration: http://en.wikipedia.org/wiki/Convention_over_configuration
__ convention_over_configuration_

How can we know that our software does what it is supposed to do?
Techniques like unit testing are good for increasing our confidence
that a program does what it is supposed to do, but ultimately they are
weak approximations. Often times it's impossible to encode all the
possible edge cases into a unit test, and if it is possible, it may be
extremely time consuming to do so. 

What do we do? Enter Formal Methods.

Formal Methods is an area of Computer Science that aims to address the problem of
verifying what software does by using mathematical models and
techniques. It's also a term that strikes fear into the hearts of
productive engineers everywhere. 

Most Formal Methods techniques involve specifications, static
checkers, runtime assertion checkers, and SMT-solvers. However,
getting them to work together is often difficult and
error-prone. Spekl is a platform for streamlining the process of
authoring, installing, and using specifications and formal methods
tools.


Installation 
========================

Installing Spekl is easy. To install, simply download the installer
for your platform from Spekl's releases `releases page
<https://github.com/jsinglet/spekl-package-manager/releases>`_ and run
it. 

At the moment, users on Linux and OSX are required to have the Git
binaries installed on your path. This requirement will be lifted in
future versions of Spekl. Windows users don't need to have Git
installed. 

Your First Verification Project
===============================

In this section we're going to see just how easy it is to verify your
programs using Spekl. Spekl supports lots of different tools like
OpenJML, SAW, and FindBugs. In this section we are going to perform
extended static checking on a small application to show you how easy
Spekl makes the verification process.

To start, create a new directory you want to store this example in::

  ~ » mkdir my-project
  ~ » cd my-project

Next, initialize the project in that directory. You can do this with
the ``spm init`` command. This command is interactive but for this
example we are going to just accept the defaults ``spm init`` uses.

.. code-block:: yaml
		
  ~ » spm init
  [spm] INFO  - [command-init]
  [spm] INFO  - [new-project] Creating new verification project...
  Project Name? [default: my project]
  Project Id? [default: my.project]
  Project Version? [default: 0.0.1]
  #
  # Basic Project Information
  #
  name            : my project
  project-id      : my.project
  version         : 0.0.1
  
  #
  # Checks
  #
  # hint: Use spm add <your-tool> to add new checks here
  #
  
  ##
  ## Example
  ##
  # checks :
  #   - name        : openjml-esc
  #     description : "OpenJML All File ESC"
  #     language    : java              # might not need this, because it is implied by the tool
  #     paths       : [MaybeAdd.java]
  
  #     tool:
  #       name      : openjml-esc
  #       version   : 0.0.3
  #       pre_check :  # stuff to do before a check
  #       post_check:  # stuff to do before a check
  
  #     # specs:
  #     #   - name: java-core
  #     #     version: 1.1.1
  
  
  Does this configuration look reasonable? [Y/n] y
  [spm] INFO  - [new-project] Writing project file to spekl.yml
  [spm] INFO  - [new-project] Done.


This command creates a file called ``spekl.yml`` in the directory you
execute ``spm init`` in. Edit that file to look like the listing,
below.

.. code-block:: yaml
  
  #
  # Basic Project Information
  #
  name            : my project
  project-id      : my.project
  version         : 0.0.1
  
  checks :                                                                                                 
    - name        : openjml-esc                                                                            
      description : "OpenJML All File ESC"                                                                 
      paths       : [MaybeAdd.java]                                                                        
                                                                                                           
      tool:                                                                                                
        name      : openjml-esc                                                                            
        pre_check :  # stuff to do before a check                                                          
        post_check:  # stuff to do before a check                                                          
  
What did we do in the listing, above? In the checks section we defined
a check called ``openjml-esc``. This is the extended static checker
provided by OpenJML, a tool that is able to check programs written in
the `JML Specification Language
<http://www.eecs.ucf.edu/~leavens/JML//index.shtml>`_. You don't need
to know JML to follow this example, but JML is an excellent modeling
language that is widely known (meaning, you should probably learn
it). 

Continuing with the example above, we defined just one check
here. Note that we have specified that we want to use OpenJML
declaratively --- we haven't specified *how* to use OpenJML. Also note
that OpenJML depends on things like SMT solvers which may be
difficult for new users to configure. We haven't needed to specify
anything about them, either.

Note that in the ``paths`` element we specified that we want to check
the file ``MaybeAdd.java``. We'll create this file next. Note that the
``paths`` element can contain a comma-separated list of paths that may
contain wildcards. You use this to specify the files you want to run a
given check on.

Next, put the following text into the file ``MaybeAdd.java`` in the
current directory

.. code-block:: java

  public class MaybeAdd {

    //@ requires 0 < a && a < 1000;
    //@ requires 0 < b && b < 1000;
    //@ ensures  0 < \result;
    public static int add(int a, int b){
	return a-b;
    }

    
    public static void main(String args[]){

	System.out.println(MaybeAdd.add(1,2));

    }

  }


In this minimal class you can see that we wrote a minimal example that
(wrongly) adds two integers. Let's see what happens when we run this
example with Spekl. To do that, first let's tell Spekl to install our tools::

  ~ » spm install

This command will kick off an installation process that will install
``z3``, ``openjml``, and ``openjml-esc``. The output will look like the following::

  [spm] INFO  - [command-install] Finding package openjml-esc in remote repository
  [spm] INFO  - [command-install] Starting install of package openjml-esc (version: 1.7.3.20150406-5)
  [spm] INFO  - [command-install] Examining dependencies...
  [spm] INFO  - [command-install] Will install the following missing packages:
  [spm] INFO  - [command-install] -  openjml (version: >= 1.7.3 && < 1.8)
  [spm] INFO  - [command-install] -  z3 (version: >= 4.3.0 && < 4.3.1)
  [spm] INFO  - [command-install] Finding package openjml in remote repository
  [spm] INFO  - [command-install] Starting install of package openjml (version: 1.7.3.20150406-1)
  [spm] INFO  - [command-install] Examining dependencies...
  [spm] INFO  - [command-install] Installing package openjml (version: 1.7.3.20150406-1)
  [spm] INFO  - [command-install] Downloading Required Assets...
  openjml-dist         : [==================================================] 100%
  [spm] INFO  - [command-install] Running package-specific installation commands
  [spm] INFO  - [command-install-scripts]  Unpacking the archive...
  [spm] INFO  - [command-install] Performing cleanup tasks...
  [spm] INFO  - [command-install] Cleaning up resources for asset  openjml-dist
  [spm] INFO  - [command-install] Writing out package description...
  [spm] INFO  - [command-install] Completed installation of package openjml (version: 1.7.3.20150406-1)
  [spm] INFO  - [command-install] Finding package z3 in remote repository
  [spm] INFO  - [command-install] Starting install of package z3 (version: 4.3.0-2)
  [spm] INFO  - [command-install] Examining dependencies...
  [spm] INFO  - [command-install] Installing package z3 (version: 4.3.0-2)
  [spm] INFO  - [command-install] Downloading Required Assets...
  Z3 Binaries for Windows : [==================================================] 100%
  [spm] INFO  - [command-install] Running package-specific installation commands
  [spm] INFO  - [command-install-scripts]  Unpacking Z3...
  [spm] INFO  - [command-install] Performing cleanup tasks...
  [spm] INFO  - [command-install] Cleaning up resources for asset  Z3 Binaries for Windows
  [spm] INFO  - [command-install] Writing out package description...
  [spm] INFO  - [command-install] Completed installation of package z3 (version: 4.3.0-2)
  [spm] INFO  - [command-install] Installing package openjml-esc (version: 1.7.3.20150406-5)
  [spm] INFO  - [command-install] Downloading Required Assets...
  [spm] INFO  - [command-install] Running package-specific installation commands
  [spm] INFO  - [command-install] Performing cleanup tasks...
  [spm] INFO  - [command-install] Writing out package description...
  [spm] INFO  - [command-install] Completed installation of package openjml-esc (version: 1.7.3.20150406-5)
  [spm] INFO  - [command-install] Installing specs....
  [spm] INFO  - [command-install] Done. Use `spm check` to check your project.

  

After that completes, we can run a check with the following command::

  ~ » spm check

The output from the check will look like the following::

  [spm] INFO  - [command-check] Running all checks for project...
  [spm] INFO  - [command-check] Running check: OpenJML All File ESC
  [spm] INFO  - Configuring solver for Z3...
  [spm] INFO  - Running OpenJML in ESC Mode...
  
  .\MaybeAdd.java:7: warning: The prover cannot establish an assertion (Postcondition: .\MaybeAdd.java:5: ) in method add
          return a-b;
          ^
  .\MaybeAdd.java:5: warning: Associated declaration: .\MaybeAdd.java:7:
      //@ ensures  0 < \result;
          ^
  .\MaybeAdd.java:13: warning: The prover cannot establish an assertion (Precondition: .\MaybeAdd.java:3: ) in method main
          System.out.println(MaybeAdd.add(1,2));
                                         ^
  .\MaybeAdd.java:3: warning: Associated declaration: .\MaybeAdd.java:13:
      //@ requires 0 < a && a < 1000;
          ^
  4 warnings
  

As you can see in the output above, the extended static checker has correctly detected that our implementation did not satisfy the specification. Let's fix that. To do that, replace the ``-`` operation in the ``MaybeAdd`` class with ``+``. Your listing should look like the following:

.. code-block:: java

  public class MaybeAdd {

    //@ requires 0 < a && a < 1000;
    //@ requires 0 < b && b < 1000;
    //@ ensures  0 < \result;
    public static int add(int a, int b){
	return a+b;
    }

    
    public static void main(String args[]){

	System.out.println(MaybeAdd.add(1,2));

    }

  }

Let's see if this works now::

  ~ » spm check

The output from the check will look like the following::

  [spm] INFO  - [command-check] Running all checks for project...
  [spm] INFO  - [command-check] Running check: OpenJML All File ESC
  [spm] INFO  - Configuring solver for Z3...
  [spm] INFO  - Running OpenJML in ESC Mode...

Since OpenJML didn't emit any errors, it means that the code we wrote satisfies the specifications.

Next Steps
==========

This is just a sample of the many things you can do with Spekl. As a user of Spekl most of your work will consist of adding and running checks. To browse some of the available checks, head over to the recipes section, here: :ref:`sec-recipes`.
