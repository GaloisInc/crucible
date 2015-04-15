<xsl:stylesheet
  version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

  <xsl:output method="xml" indent="yes" encoding="UTF-8"/>

  <xsl:template match="@*|node()">
        <xsl:copy>
            <xsl:apply-templates select="@*|node()"/>
        </xsl:copy>
  </xsl:template>

  <xsl:template match="testcase">
    <testcase>
       <xsl:copy-of select="@*"/>
       <xsl:attribute name="classname">
	 <xsl:value-of select="(./ancestor::testsuite)[1]/@name"/>
	 <xsl:for-each select="(./ancestor::testsuite)[position()>1]">.<xsl:value-of select="@name"/></xsl:for-each>
       </xsl:attribute>
       <xsl:apply-templates select="*"/>
    </testcase>
  </xsl:template>

</xsl:stylesheet>
