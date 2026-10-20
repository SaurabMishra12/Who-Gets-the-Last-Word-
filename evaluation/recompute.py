"""Offline checks against saved records. No inference, network, or model dependency."""
import csv
import json
import math
import statistics
import sys
from collections import Counter, defaultdict
from pathlib import Path
from answer_metrics import eval_answer, normalize_answer

ROOT = Path(__file__).resolve().parents[1]
def load(path): return json.loads((ROOT/path).read_text())
def same(a,b,label):
    if abs(a-b)>1e-7: raise ValueError(f'{label}: {a} != {b}')
def score(answer,target):
    vals=[eval_answer(answer or 'noanswer',g) for g in [target['answer'],*target.get('aliases',[])]]
    return {'em':100*max(v[0] for v in vals),'f1':100*max(v[1] for v in vals)}
def vote(states):
    pool=[s['answer'] for s in states if s.get('kind','valid')=='valid' and s.get('answer') and normalize_answer(s['answer'])!='noanswer']
    if not pool:return 'noanswer'
    counts=Counter(normalize_answer(a) for a in pool);winner=max(counts,key=counts.get)
    return next(a for a in pool if normalize_answer(a)==winner)
def mcnemar(a,b):
    wins=sum(x and not y for x,y in zip(a,b));losses=sum(y and not x for x,y in zip(a,b));d=wins+losses
    return {'wins':wins,'losses':losses,'p':min(1.,2*sum(math.comb(d,k) for k in range(min(wins,losses)+1))/2**d)}

def main():
    report={'scope':'Offline answer scoring, saved readout reconstruction, point estimates, exact paired binary tests and archive counts. No claim of new inference or full experiment reproduction.'};checks=0
    targets=load('configs/two_wiki_historical_targets.json')
    for name,refs in [('historical_readouts',targets),('new_peer_private',load('configs/peer_private_targets.json')),('replication_peer_private',load('configs/development_targets.json')),('packet_ablation',load('configs/development_targets.json'))]:
        records=load(f'results/two_wiki/{name}.json')
        if len({r['qid'] for r in records})!=len(records):raise ValueError('Duplicate question IDs')
        totals=defaultdict(list)
        for r in records:
            for condition,saved in r['scores'].items():
                values=score(saved['answer'],refs[r['qid']])
                for m in ['em','f1']:same(saved[m],values[m],name+':'+condition+':'+m);checks+=1
                totals[condition].append(values)
        report[name]={'n':len(records),'metrics':{c:{'em':statistics.mean(s['em'] for s in ss),'f1':statistics.mean(s['f1'] for s in ss),'correct':sum(s['em']==100 for s in ss)} for c,ss in totals.items()}}
        if 'peer_all' in totals:
            report[name]['peer_minus_private']=mcnemar([s['em']==100 for s in totals['peer_all']],[s['em']==100 for s in totals['private_all']])
    for family,name in [('peer_private','new_peer_private'),('development','replication_peer_private')]:
        records={r['qid']:r for r in load(f'results/two_wiki/{name}.json')}
        for wrapper in load(f'raw_outputs/{family}/results.json'):
            r=wrapper['result'];q=r['question_key'];states=r['states'];initial=r['initial'] if 'initial' in r else load('raw_outputs/peer_private/initial_states.json')[q]['initial']
            slates={'peer_all':states['peer'],'private_all':states['private']}
            slates.update({'R0_all':initial,'peer_sink_R0_leaves':[initial[0],states['peer'][1],initial[2]],'peer_sink_private_leaves':[states['private'][0],states['peer'][1],states['private'][2]]})
            if 'full_union' in r:slates['full_union']=[r['full_union']]
            for c,ss in slates.items():
                if vote(ss)!=records[q]['scores'][c]['answer']:raise ValueError('Raw readout mismatch: '+q+':'+c)
                checks+=1
    # Historical sink identity and all stored official readouts.
    hist_targets=load('configs/two_wiki_historical_targets.json');sink_matches=0
    for folder in ['results','imported_results']:
        for wrapper in load(f'raw_outputs/two_wiki_historical/{folder}.json'):
            r=wrapper['result'];arms=r['arms'];target=hist_targets[r['question_key']]
            if arms['instar']['hub_request_key']!=arms['dense']['hub_request_key']:raise ValueError('Sink request identity changed')
            sink_matches+=1
            for name,arm in arms.items():
                for rule,answer in [('abstention_aware',vote(arm['states'])),('sink1',arm['states'][0 if name=='full_union' else 1].get('answer'))]:
                    values=score(answer,target)
                    for m in ['em','f1']:same(values[m],arm['readouts'][rule][m],name+':'+rule);checks+=1
    report['historical_identical_sink_requests']=sink_matches
    hotpot_refs={r['id']:r for r in load('data/hotpot_evaluation_references.json')}
    hp=[]
    for family in ['hotpot_controlled','hotpot_controller','hotpot_e3_v2']:
        for p in sorted((ROOT/'raw_outputs'/family).glob('E*.json')):
            rows=json.loads(p.read_text());n=0
            for r in rows:
                for c,condition in r['conditions'].items():
                    values=score(condition['answer'],hotpot_refs[r['id']])
                    for m in ['em','f1']:same(values[m],condition[m],p.name+':'+c);checks+=1
                    n+=1
            hp.append({'file':str(p.relative_to(ROOT)),'questions':len(rows),'conditions_scored':n})
    report['hotpot_original_scores']=hp
    for r in load('results/hotpot_readouts/question_readouts.json'):
        values=score(r['answer'],hotpot_refs[r['question_id']])
        for m in ['em','f1']:same(values[m],r[m],'hotpot_readout:'+m);checks+=1
        rs=[{'answer':a,'kind':'refusal' if refused else 'valid'} for a,refused in zip(r['final_answers'],r['final_refusals'])]
        if r['readout']=='abstention_aware' and vote(rs)!=r['answer']:raise ValueError('Hotpot AA readout mismatch')
    report['hotpot_readout_rows']=18000
    report['p5']={}
    for p in sorted((ROOT/'raw_outputs/p5_communication_control').glob('*.json')):
        rows=json.loads(p.read_text());report['p5'][p.stem]={'n':len(rows),'correct':sum(r['is_correct'] for r in rows),'mean_proxy':statistics.mean(r['total_tokens_transmitted'] for r in rows),'mean_rounds':statistics.mean(r['halt_round'] for r in rows)}
    if sorted(r['correct'] for r in report['p5'].values())!=[91,91,93,93]:raise ValueError('P5 counts changed')
    report['P1_reported_seed_summary']={}
    for method,r in load('results/reasoning/final_results.json').items():
        same(statistics.mean(r['all_accuracies']),r['accuracy_mean'],method+' mean')
        same(statistics.stdev(r['all_accuracies']),r['accuracy_std'],method+' SD')
        report['P1_reported_seed_summary'][method]={'accuracy_percent':100*r['accuracy_mean'],'sd_percent':100*r['accuracy_std'],'communication_proxy':r['token_cost_mean'],'validation':'Seed-array arithmetic; original per-seed row selection remains historical.'}
    report['checks']=checks;report['status']='PASS'
    output=Path(sys.argv[1]) if len(sys.argv)>1 else Path('/tmp/lastword_recomputed.json')
    output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'PASS','checks':checks,'output':str(output),'train_peer_correct':report['new_peer_private']['metrics']['peer_all']['correct'],'development_peer_correct':report['replication_peer_private']['metrics']['peer_all']['correct']}))
if __name__=='__main__':main()
