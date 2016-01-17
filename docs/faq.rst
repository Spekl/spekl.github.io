.. _sec-faq:

Frequently Asked Questions
============================

.. _q-windows:

I just installed Spekl but it's not appearing on my path. Do I need to
manually add it?
-------------------------------------------------------------------------------
Spekl's installer automatically adds the path to ``spm`` to your
path. On platforms like Windows and OSX, the easiest way to refresh
your path is to restart the shell you use (CMD.EXE or Cygwin,
Terminal.app, etc). This should enable you to use the ``spm`` tool on
the command line. On Linux platforms the path is not automatically
updated and must be added to your ``.profile`` or shell init
scripts. In case the automatic path modification doesn't work (or if
you are on Linux), the following list below details where Spekl is
installed on various platforms:

- Windows: ``C:\Program Files (x86)\spm``
- OSX: ``/Applications/spm``
- Linux: ``/opt/spm``


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
If you still have the local directory you created the project in you
can just use your normal ``spm publish`` commands.

If you are on a different machine (or you'd like to give access to
someone else) just go to our Spekl page on GitHub, here:
http://github.com/Spekl. Find your repo and do a normal ``git clone``
as with any other Git repository. Note however that you should not do
an explicit ``git push`` -- rely on ``spm publish`` do do that work
for you. 


.. _q-broken:

Help! Something is Broken! Spekl Isn't Working, etc
----------------------------------------------------
The first thing you should always do is delete the ``.spm`` directory
and try installing with ``spm install`` again. If that doesn't work,
please open an issue over on our GitHub `Issue Tracker <https://github.com/jsinglet/spekl-package-manager/issues>`_.
