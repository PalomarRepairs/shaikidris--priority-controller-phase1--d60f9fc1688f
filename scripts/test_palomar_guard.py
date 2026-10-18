"""Regression checks for release bindings against the exact upstream parser."""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import yaml
import palomar_guard as guard

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--pipeline', type=Path, required=True)
parser.add_argument('--scratch-root', type=Path, required=True)
args = parser.parse_args()
sys.path.insert(0, str(args.pipeline.resolve()))
from scripts import submission_contract as contract
from scripts import render_challenge as renderer
SOURCE = Path(__file__).resolve().parents[1]

class GuardRegression(unittest.TestCase):
    def inputs(self):
        return dict(repository='example/project', commit='a'*40,
            pipeline_commit=guard.PIPELINE, request_id='abcdef123456',
            mode='full', execution_profile=guard.PROFILE,
            options=json.dumps({'comparator_config_path':'entries/P01/comparator.json',
                'authorization_relationship':'I am a responsible author or maintainer'}))

    def test_valid_request(self):
        self.assertEqual(guard.validate_inputs(contract, self.inputs()), 'abcdef123456')

    def test_bad_request_identifier(self):
        inputs=self.inputs(); inputs['request_id']='phase1-release-too-long'
        with self.assertRaisesRegex(Exception,'twelve'):
            guard.validate_inputs(contract, inputs)

    def test_missing_authorization(self):
        inputs=self.inputs();inputs['options']='{"comparator_config_path":"entries/P01/comparator.json"}'
        with self.assertRaisesRegex(ValueError,'authorization'):
            guard.validate_inputs(contract, inputs)

    def test_invalid_source_commit(self):
        inputs=self.inputs();inputs['commit']='main'
        with self.assertRaisesRegex(ValueError,'source commit'):
            guard.validate_inputs(contract, inputs)

    def test_wrong_pipeline(self):
        inputs=self.inputs();inputs['pipeline_commit']='0'*40
        with self.assertRaisesRegex(ValueError,'pipeline pin'):
            guard.validate_inputs(contract, inputs)

    def test_wrong_mode(self):
        inputs=self.inputs();inputs['mode']='preflight'
        with self.assertRaisesRegex(ValueError,'full mode'):
            guard.validate_inputs(contract, inputs)

    def test_workflow_bindings(self):
        workflow=yaml.safe_load((SOURCE/guard.WORKFLOW).read_text())
        guard.validate_workflow(workflow)
        for mutation in ['uses','commit','needs','bytecode']:
            bad=copy.deepcopy(workflow)
            if mutation=='commit':bad['jobs']['verify']['with']['commit']='${{ github.sha }}'
            elif mutation=='needs':del bad['jobs']['verify']['needs']
            elif mutation=='bytecode':del bad['jobs']['guard']['env']['PYTHONDONTWRITEBYTECODE']
            else:bad['jobs']['verify']['uses']='wrong/workflow@'+'0'*40
            with self.assertRaises(ValueError):guard.validate_workflow(bad)

    def test_embedded_orcid_rejected(self):
        valid=yaml.safe_load((SOURCE/'formalization.yaml').read_text())
        for field in ['authors','responsible_maintainers']:
            bad=copy.deepcopy(valid);bad['project'][field]=['Researcher (ORCID: 0009-0009-9699-9712)']
            with tempfile.TemporaryDirectory(dir=args.scratch_root) as tmp:
                path=Path(tmp)/'formalization.yaml';path.write_text(yaml.safe_dump(bad))
                with self.assertRaisesRegex(Exception,'ORCID'):contract.load_formalization_metadata(path)

    def test_entry_selection(self):
        for comparator,metadata in [('entries/P01/comparator.json','formalization.yaml'),
                                    ('entries/P05/comparator.json','entries/P05/formalization.yaml')]:
            data=contract.load_formalization_metadata(SOURCE/metadata)
            guard.validate_selection(SOURCE,data,comparator)
            bad=copy.deepcopy(data);bad['alignment']['statements'].pop()
            with self.assertRaisesRegex(ValueError,'selections differ'):
                guard.validate_selection(SOURCE,bad,comparator)

    def test_manifest_conflict(self):
        base=json.loads((SOURCE/'lake-manifest.json').read_text())
        package=copy.deepcopy(base['packages'][0]);package['rev']='0'*40
        with self.assertRaisesRegex(Exception,'conflicts'):
            renderer.merge_renderer_manifest(base, {'packages':[package]}, 'a'*40)

    def test_missing_selected_module(self):
        with tempfile.TemporaryDirectory(dir=args.scratch_root) as tmp:
            root=Path(tmp);config=json.loads((SOURCE/'entries/P01/comparator.json').read_text())
            (root/'comparator.json').write_text(json.dumps(config))
            metadata=contract.load_formalization_metadata(SOURCE/'formalization.yaml')
            with self.assertRaisesRegex(ValueError,'module is missing'):
                guard.validate_selection(root,metadata,'comparator.json')

    def test_clean_commit_binding(self):
        # This isolated fixture commit is never a submission candidate.
        with tempfile.TemporaryDirectory(dir=args.scratch_root) as tmp:
            root=Path(tmp)
            def git(*argv):
                return subprocess.check_output(['git','-C',str(root),*argv],text=True,stderr=subprocess.DEVNULL).strip()
            git('init');(root/'fixture.txt').write_text('guard fixture\n');git('add','fixture.txt')
            git('-c','user.name=Guard Regression','-c','user.email=guard@example.invalid',
                '-c','core.hooksPath=/dev/null','-c','commit.gpgsign=false','commit','-m','Guard fixture')
            commit=git('rev-parse','HEAD');guard.require_snapshot(root,commit)
            with self.assertRaisesRegex(ValueError,'requested commit'):guard.require_snapshot(root,'0'*40)
            (root/'fixture.txt').write_text('dirty\n')
            with self.assertRaisesRegex(ValueError,'dirty'):guard.require_snapshot(root,commit)

if __name__=='__main__':
    unittest.main(argv=[sys.argv[0]],verbosity=2)
