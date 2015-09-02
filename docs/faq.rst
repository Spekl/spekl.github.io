.. _sec-faq:

Frequently Asked Questions
============================

.. _q-update-auth:

I need to update my publishing information/authentication info, how do I do it?
-------------------------------------------------------------------------------
All authentication information is stored under the ``author``
configuration element. See the next question (:ref:`q-multiple-authors`) for more information on
how to get this to work. 

.. _q-multiple-authors:

My project has multiple authors, how can we all author together?
----------------------------------------------------------------
The author attribute in the configuration supports any number of
authors. For it to work, you must first add the user to your team on
GitHub. To do that, go to the team administration page for your
project: https://github.com/orgs/Spekl/teams

After you add the user to your team, fill in their name and email in
the author configuration element, for example:

.. code-block:: yaml

  name        : maybe-add-specs          # name of the package
  version     : 0.0.1       # version of the package
  kind        : spec                     # one of tool or spec(s)
  description : a short description

  author:
    - name: John L. Singleton
      email: jsinglet@gmail.com
    - name: Some Other User
      email: otheruser@gmail.com

When you run ``spm publish`` you will be prompted to select the user
you want to use for authentication. 

.. _q-update:

How Do I Update My Specs/Tools After I Publish Them?
----------------------------------------------------

