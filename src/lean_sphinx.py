from docutils import nodes
from docutils.parsers.rst import Directive
from sphinx.builders import Builder
from sphinx.directives.code import CodeBlock
from sphinx.errors import SphinxError
import os, os.path, fnmatch, subprocess, shutil
import codecs
import urllib
import re
import pathlib

try:
    urlquote = urllib.parse.quote
except:
    # Python 2
    def urlquote(s, safe='/'):
        return urllib.quote(s.encode('utf-8'), safe)


# "Try it!" button

class lean_code_goodies(nodes.General, nodes.Element): pass

def mk_try_it_uri(code):
    # The default project on live.lean-lang.org ("Latest Mathlib") is used
    # when no `project=` fragment param is given, so it's omitted here.
    uri = 'https://live.lean-lang.org/#code='
    uri += urlquote(code, safe='~()*!.\'')
    return uri

def process_lean_nodes(app, doctree, fromdocname):
    for node in doctree.traverse(nodes.literal_block):
        if node['language'] != 'lean4': continue

        new_node = lean_code_goodies()
        new_node['full_code'] = node.rawsource
        if len(node['names']) > 0:
            name = node['names'][0]
        else:
            name = 'unnamed_{0}'.format(node.line)
        new_node['name'] = name
        new_node['example_file'] = '{0}/{1}.lean'.format(fromdocname, name)
        node.replace_self([new_node])

        code = node.rawsource
        m = re.search(r'--[^\n]*BEGIN[^\n]*\n(.*)--[^\n]*END', code, re.DOTALL)
        if m:
            node = nodes.literal_block(m.group(1), m.group(1))
            node['language'] = 'lean'
        new_node += node

        if app.builder.name.startswith('epub'):
            new_node.replace_self([node])

def html_visit_lean_code_goodies(self, node):
    self.body.append(self.starttag(node, 'div', style='position: relative'))
    self.body.append("<div style='position: absolute; right: 0; top: 0; padding: 1ex'>")
    attrs = {}
    if 'example_file' in node:
        attrs['tryitFile'] = '../examples/' + node['example_file']
    self.body.append(self.starttag(node, 'a', target='_blank', href=mk_try_it_uri(node['full_code']), **attrs))
    self.body.append('try it!</a></div>')

def html_depart_lean_code_goodies(self, node):
    self.body.append('</div>')

def latex_visit_lean_code_goodies(self, node):
    pass

def latex_depart_lean_code_goodies(self, node):
    pass

# Extract code snippets for testing.

class LeanTestBuilder(Builder):
    '''
    Extract ``..code-block:: lean`` directives for testing.
    '''
    name = 'leantest'

    def init(self):
        self.written_files = set()

    def write_doc(self, docname, doctree):
        for node in doctree.traverse(lean_code_goodies):
            fn = os.path.join(self.outdir, '{0}_{1}.lean'.format(docname, node['name']))
            self.written_files.add(fn)
            out = codecs.open(fn, 'w', encoding='utf-8')
            out.write(node['full_code'])

    def finish(self):
        for root, _, filenames in os.walk(self.outdir):
            for fn in fnmatch.filter(filenames, '*.lean'):
                fn = os.path.join(root, fn)
                if fn not in self.written_files:
                    os.remove(fn)

        # Copy the extracted blocks into the Lake project so they're checked
        # against Lean 4 + mathlib4 (via `lake build`) instead of a bare `lean`
        # invocation, which can't resolve mathlib imports.
        lean_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'lean'))
        check_dir = os.path.join(lean_dir, 'CrashCourse', 'Examples', 'RstBlocks')
        if os.path.isdir(check_dir):
            shutil.rmtree(check_dir)
        os.makedirs(check_dir, exist_ok=True)
        for fn in self.written_files:
            shutil.copy(fn, os.path.join(check_dir, os.path.basename(fn)))

        proc = subprocess.Popen(['lake', 'build'], cwd=lean_dir,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        stdout, _ = proc.communicate()
        output = stdout.decode('utf-8')
        errors = '\n'.join(l for l in output.split('\n') if 'error:' in l)
        if errors != '': raise SphinxError('\nlake exited with errors:\n{0}\n'.format(errors))
        retcode = proc.wait()
        if retcode: raise SphinxError('lake exited with error code {0}:\n{1}'.format(retcode, output))

    def prepare_writing(self, docnames): pass

    def get_target_uri(self, docname, typ=None):
        return ''

    def get_outdated_docs(self):
        return self.env.found_docs

# Extract code snippets for testing.

class LeanExamplesBuilder(Builder):
    '''
    Extract ``..code-block:: lean`` examples.
    '''
    name = 'examples'

    def write_doc(self, docname, doctree):
        for node in doctree.traverse(lean_code_goodies):
            if 'name' not in node: continue
            d = pathlib.Path(self.outdir, docname)
            d.mkdir(parents=True, exist_ok=True)
            with (d / '{0}.lean'.format(node['name'])).open('w', encoding='utf-8') as out:
                out.write(node['full_code'])

    def prepare_writing(self, docnames): pass

    def get_target_uri(self, docname, typ=None):
        return ''

    def get_outdated_docs(self):
        return self.env.found_docs

def setup(app):
    app.add_node(lean_code_goodies,
        html=(html_visit_lean_code_goodies, html_depart_lean_code_goodies),
        latex=(latex_visit_lean_code_goodies, latex_depart_lean_code_goodies))
    app.connect('doctree-resolved', process_lean_nodes)

    app.add_builder(LeanTestBuilder)
    app.add_builder(LeanExamplesBuilder)

    return {'version': '0.1'}
