"""Render companion plots from released CSV; no inference or external data."""
import csv
import sys
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, Circle

root=Path(__file__).resolve().parent
out=Path(sys.argv[1]) if len(sys.argv)>1 else Path('/tmp/lastword-figures');out.mkdir(parents=True,exist_ok=True)
rows=list(csv.DictReader((root/'plot_data.csv').open()))
plt.rcParams.update({'font.size':9,'axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42})
def save(fig,name):
    fig.savefig(out/(name+'.pdf'),bbox_inches='tight');fig.savefig(out/(name+'.png'),dpi=160,bbox_inches='tight');plt.close(fig)
def subset(fig,panel):return [r for r in rows if r['figure']==str(fig) and r['panel']==panel]
def bars(ax,data,title,ylabel):
    ax.bar(range(len(data)),[float(r['y']) for r in data],color='#315a7d')
    ax.set_xticks(range(len(data)),[r['label'].replace('_','\n') for r in data],fontsize=7);ax.set_title(title);ax.set_ylabel(ylabel)

fig,axes=plt.subplots(1,3,figsize=(12,3.4))
positions=[(-.8,0),(0,.85),(.8,0)]
for ax,edges,title in [(axes[0],[(0,1),(2,1)],'Incoming star: 2 deliveries, 1 update'),(axes[1],[(i,j) for i in range(3) for j in range(3) if i!=j],'Dense: 6 deliveries, 3 updates')]:
    for i,j in edges:ax.add_patch(FancyArrowPatch(positions[i],positions[j],arrowstyle='->',mutation_scale=13,shrinkA=23,shrinkB=23,connectionstyle='arc3,rad=0.09'))
    for i,pos in enumerate(positions):ax.add_patch(Circle(pos,.18,color='#315a7d' if i==1 else '#e0e5e9'));ax.text(*pos,str(i),ha='center',va='center',color='white' if i==1 else 'black')
    ax.set(xlim=(-1.2,1.2),ylim=(-.45,1.3),title=title);ax.set_aspect('equal');ax.axis('off')
axes[2].text(.03,.9,'Readout determines whose answer counts',fontsize=11,transform=axes[2].transAxes)
axes[2].text(.03,.72,'Sink: use Agent 1\nFallback: initial leaves if sink abstains\nVote: all selected final states\nAA vote: remove abstentions first',va='top',linespacing=1.7,transform=axes[2].transAxes);axes[2].axis('off')
fig.tight_layout();save(fig,'figure_1_execution_and_readout')
fig,axes=plt.subplots(1,3,figsize=(14,3.8))
for rule,marker in [('Sink','o'),('SP','s'),('AA','^')]:
    rr=[r for r in subset(2,'quality_cost') if r['label'].endswith('_'+rule)]
    axes[0].scatter([float(r['x']) for r in rr],[float(r['y']) for r in rr],label=rule,marker=marker)
axes[0].set(xlabel='Logical input + output tokens / question',ylabel='Answer EM (%)',title='130-question extension');axes[0].legend()
rr=[r for r in subset(2,'quality_cost') if r['label'].startswith(('instar_','dense_'))]
bars(axes[1],rr,'Readout-dependent ranking','Answer EM (%)')
bars(axes[2],subset(2,'leaf_attribution'),'Dense vote correct; sink wrong','Correct among 28 questions')
fig.tight_layout();save(fig,'figure_2_two_wiki')
fig,axes=plt.subplots(1,3,figsize=(14,3.8))
bars(axes[0],subset(3,'retrieval_strata'),'Retrieved gold-title coverage','Questions (%)')
bars(axes[1],subset(3,'readout_em'),'Partitioned HotpotQA: EM','Answer EM (%)')
bars(axes[2],subset(3,'readout_f1'),'Partitioned HotpotQA: answer F1','Answer F1 (%)')
fig.tight_layout();save(fig,'figure_3_hotpot_readout')
fig,axes=plt.subplots(1,3,figsize=(14,3.8))
bars(axes[0],subset(4,'factorial_volume'),'P2b: factorial arms','Stored communication units')
for r in subset(4,'support_sweep'):
    axes[1].scatter(float(r['x']),float(r['y']),s=25,marker='^' if 'PPO' in r['label'] else 'o',color='#b57232' if 'PPO' in r['label'] else '#315a7d')
axes[1].set(xlabel='Stored communication units',ylabel='Accuracy (%)',title='P4: arithmetic-template diagnostics')
for r in subset(4,'routing_stopping'):
    axes[2].scatter(float(r['x']),float(r['y']),s=55);axes[2].annotate(r['label'].replace('_stream','').replace('_',' '),(float(r['x']),float(r['y'])),xytext=(0,8 if 'Static' in r['label'] else -18),textcoords='offset points',ha='center',fontsize=6)
axes[2].set(xlabel='Word-based communication proxy',ylabel='Accuracy (%)',title='P5: routing and stopping',xlim=(5,55),ylim=(88,96))
fig.tight_layout();save(fig,'figure_4_arithmetic_attribution')
print('Rendered four companion figures to '+str(out))
