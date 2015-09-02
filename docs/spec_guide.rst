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


Publishing Specifications
=========================


After You've Published Your Specs
---------------------------------
After you've published your specs, you may want 


Advanced Topics in Specification Authoring
==========================================

.. _sec-all-packages-are-git-repos:

Remember, All Packages are also Git Repositories!
-------------------------------------------------


Layering Specifications
-----------------------


Refreshing Layered Specifications
---------------------------------





