{-# LANGUAGE QuasiQuotes #-}


module Crux.UI.IndexHtml where

import           Data.Text (Text)
-- raw-strings-qq
import Text.RawString.QQ


indexHtml :: Text
indexHtml = [r|<!DOCTYPE html>
<html>
<head>

<script src="jquery.min.js"></script>
<script src="source.js"></script>
<script src="report.js"></script>
<script>
function drawLines() {
  var i
  var dom = $('<ol/>')
  for (i = 0; i < lines.length; ++i) {
    var li = $('<li/>').attr('id','line-' + (i+1))
                       .addClass('line')
                       .text(lines[i])
    dom.append(li)
  }
  return dom
}

function getLine(n) { return $('#line-' + n) }

function drawStatus(status) {
  return $('<div/>')
         .addClass('tag')
         .text(status)
                    .addClass('highlight-' + status)
}

function drawCounterExample(e) {
  if (e === null) return
  jQuery.each(e, function(ix,v) {
    getLine(v.line).append($('<span/>')
                   .addClass('ctr-example').text(v.val))
  })
}



function drawPath(path) {
  $('.path').remove()
  jQuery.each(path,function(ix,step) {
    var branch = step.loc
    var ln = getLine(branch)

    var pre = ""
    if (step.loop.length > 1) {
      pre = "("
      for (i = 0; i < step.loop.length - 1; ++i) {
        pre += step.loop[i]
        pre += (i === step.loop.length - 2) ? ')' : ','
      }
   }

    var tag = $('<span/>')
              .addClass('path')
              .append( $('<span/>').text(pre + step.loop[step.loop.length-1])
                     , $('<sup/>').text(ix+1)
                     )
    ln.append(tag)
  })
}

function summarizePath(path) {
  var it = $('<div/>')
  var fst = true
  jQuery.each(path,function(ix,branch) {
    let msg = (fst ? '' : ', ') + branch.line + '(' + branch.tgt + ')'
    it.append($('<span/>').text(msg))
    fst = false
  })
  return it
}



function drawGoals() {
  var dom = $('<div>').addClass('goals')

  if (goals.length === 0) dom.append($('<span/>').text('Nothing to prove.'))

  jQuery.each(goals, function(gNum,g) {
    var li = $('<div/>')
            .css('cursor','pointer')
            .append( drawStatus(g.status)
                   , $('<span/>').text(g.goal)
                   )
    li.click(function() {
      $('.selected').removeClass('selected')
      li.addClass('selected')
      $('.ctr-example').remove()
      $('.asmp-lab').remove()
      $('.line').removeClass('highlight-ok')
                .removeClass('highlight-fail')
                .removeClass('highlight-assumed')
                .removeClass('highlight-unknown')
     jQuery.each(g.assumptions, function(ix,a) {
        var lnName = a.line
        if (lnName !== g.location) {
            getLine(lnName).addClass('highlight-assumed')
        }
      })
      if (g.location !== null)
        var it = getLine(g.location)
        it.addClass('highlight-' + g.status)
        it[0].scrollIntoView({behavior:'smooth', block:'center'})
      drawCounterExample(g['counter-example'])
      if(g.path) drawPath(g.path)
    })
    dom.append(li)
  })

  return dom
}

$(document).ready(function() {
  $('#source-code').append(drawLines())
  $('#nav-bar').append(drawGoals())
})
</script>
<style>
html { height: 100%; padding: 0; margin: 0; }
body { height: 100%; padding: 0; margin: 0; }

#nav-bar {
  width: 25%;
  float: left;
  height: 90%;
  overflow: auto;
}

#source-code {
  float: right;
  width: 74%;
  font-family: monospace;
  white-space: pre;
  height: 90%;
  overflow: auto;
  font-size: 16px;
}

#source-code>ol {
  counter-reset: item;
}

#source-code>ol>li {
  list-style-type: none;
  counter-increment: item;
}

#source-code>ol>li:hover {
  background-color: #ccf;
}

#source-code>ol>li:before {
  display: inline-block;
  width: 4em;
  text-align: right;
  content: counter(item);
  margin-right: 1em;
  font-size: 10px;
  font-style: italic;
  color: #999;
}

.goals { margin: 5px; }

.highlight-ok      { background-color: green; color: white; }
.highlight-fail    { background-color: red;  color: white; }
.highlight-unknown { background-color: yellow; color: black; }
.highlight-assumed { background-color: cyan; color: black; }
.ctr-example {
  margin: 5px;
  background-color: #ff0000;
  color: white;
  font-weight: bold;
  padding-left: 2px;
  padding-right: 2px;
  border-radius: 5px;
  font-size: smaller;
}

.asmp-lab {
  border: 1px solid black;
  margin: 5px;
  background-color: #eee;
  padding-left: 2px;
  padding-right: 2px;
  border-radius: 5px;
  font-size: smaller;
}

.selected {
  background-color: #ccf;
}

.path {
  margin-right: 1em;
}

.path>span {
  font-weight: bold;
  background-color: orange;
  border-radius: 10px;
  margin: 2px;
  padding: 2px;
}

.path>sup {
  color: #666;
  font-style: italic;
  font-size: small;
  font-weight: normal;
}

.tag {
  font-weight: bold;
  font-family: monospace;
  display: inline-block;
  margin: 2px;
  padding: 2px;
  padding-left: 4px;
  padding-right: 4px;
  text-align: center;
  border-radius: 2px;
  width: 4em;
}

</style>
</head>
<body><div id="nav-bar"></div
><div id="source-code"></div
></body>
</html>
|]
