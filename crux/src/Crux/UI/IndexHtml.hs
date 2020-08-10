{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Crux.UI.IndexHtml where

import           Data.Text (Text)
-- raw-strings-qq
import Text.RawString.QQ


indexHtml :: Text
indexHtml = [r|
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">

<script src="jquery.min.js"></script>
<script src="source.js"></script>
<script src="report.js"></script>
<script>

var fileObjs = {}
var nextId = 0

function getFile(loc) {
  var obj = fileObjs[loc.file]
  return obj ? $(obj.dom) : $([])
}

function getLine(loc) { return getFile(loc).find('#line-' + loc.line) }

function showFile(name) {
  var obj = fileObjs[name]
  if (!obj) return

  $('.source-file').hide()
  $('.file-btn').removeClass('selected')
  obj.dom.show()
  obj.btn.addClass('selected')
}

function drawSourceFile(file) {
  var obj = fileObjs[file.name]
  if (!obj) {
    obj = { id: 'file_' + nextId }
    ++nextId
    fileObjs[file.name] = obj
  }

  var dom = drawLines(file.lines)
            .attr('id',obj.id)
            .addClass('source-file')
  dom.hide()

  var btn = $('<div/>')
            .text(file.label)
            .addClass('clickable file-btn')
  obj.dom = dom
  obj.btn = btn

  btn.click(function() { showFile(file.name) })

  return { btn: btn, dom: dom }
}

function drawLines(lines) {
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


function drawStatus(status) {
  return $('<div/>')
         .addClass('tag')
         .text(status)
                    .addClass('highlight-' + status)
}

function drawCounterExample(e) {
  if (e === null) return
  jQuery.each(e, function(ix,v) {
    getLine(v.loc).append($('<span/>')
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
            .addClass('clickable')
            .append( drawStatus(g.status)
                   , $('<span/>').text(g.goal)
                   )
    li.click(function() {
      $('.highlight-assumed').removeClass('highlight-assumed')
      $('.selected').removeClass('selected')
      li.addClass('selected')
      $('.ctr-example').remove()
      $('.asmp-lab').remove()
      $('.line').removeClass('highlight-ok')
                .removeClass('highlight-fail')
                .removeClass('highlight-assumed')
                .removeClass('highlight-unknown')
     jQuery.each(g.assumptions, function(ix,a) {
        var lnName = a.loc
        if (!lnName) return true
        if (!lnName.file) return true

         var obj = fileObjs[lnName.file]
         if(obj) obj.btn.addClass('highlight-assumed')

        if (lnName.file !== g.location.file || lnName.line !== g.location.line) {
          var ln = getLine(lnName)
          ln.addClass('highlight-assumed')

          // var note = $('<div/>')
          //            .addClass('asmp-lab')
          //            .text(a.text)
          // ln.append(note)
        }
      })
      if (g.location !== null) {
        showFile(g.location.file)
        var it = getLine(g.location)
        it.addClass('highlight-' + g.status)
        it[0].scrollIntoView({behavior:'smooth', block:'center'})
      }
      drawCounterExample(g['counter-example'])
      if(g.path) drawPath(g.path)
    })
    dom.append(li)
  })

  return dom
}

$(document).ready(function() {
  var i
  var srcPane = $('#source-pane')
  var filePane = $('#file-pane')
  jQuery.each(sources, function(ix,file) {
    ui = drawSourceFile(file)
    srcPane.append(ui.dom)
    filePane.append(ui.btn)
  })

  $('#nav-bar').append(drawGoals())
})
</script>
<style>
html { height: 100%; padding: 0; margin: 0; }
body { height: 100%; padding: 0; margin: 0; }

.clickable {
  cursor: pointer;
}

#nav-bar {
  width: 25%;
  float: left;
  height: 90%;
  overflow: auto;
}

#right-pane {
  float: right;
  width: 74%;
}

#source-pane {
  font-family: monospace;
  white-space: pre;
  height: 90%;
  overflow: auto;
  font-size: 16px;
}

.file-btn {
  border: 1px solid black;
  border-radius: 5px;
  display: inline-block;
  margin: 2px;
  padding: 2px;
}


ol.source-file {
  counter-reset: item;
  padding: 0;
}

ol.source-file>li {
  list-style-type: none;
  counter-increment: item;
}

ol.source-file>li:hover {
  background-color: #ccf;
}

ol.source-file>li:before {
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

.highlight-ok      { background-color: green !important; color: white; }
.highlight-fail    { background-color: red !important;  color: white; }
.highlight-unknown { background-color: yellow !important; color: black; }
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
><div id="right-pane"
  ><div id="file-pane"></div
  ><div id="source-pane"></div
></div
></body>
</html>
|]
